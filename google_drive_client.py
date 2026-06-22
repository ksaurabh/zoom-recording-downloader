import os
import json
from datetime import datetime
from google.oauth2.credentials import Credentials
from google.auth.transport.requests import Request
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
from googleapiclient.http import MediaFileUpload
from googleapiclient.errors import HttpError
import re
import time

class Color:
    PURPLE = "\033[95m"
    CYAN = "\033[96m"
    DARK_CYAN = "\033[36m"
    BLUE = "\033[94m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    RED = "\033[91m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"
    END = "\033[0m"

SUCCESS_PAGE = """
<!DOCTYPE html>
<html>
<head>
    <title>Authentication Successful</title>
</head>
<body>
    <h1>Zoom Recording Downloader</h1>
    <p>Authentication successful! You may close this window.</p>
</body>
</html>
"""

class GoogleDriveClient:
    SCOPES = [
        'https://www.googleapis.com/auth/drive.file',
        'https://www.googleapis.com/auth/drive.metadata',
        'https://www.googleapis.com/auth/drive.appdata'
    ]

    def __init__(self, config):
        self.config = config
        self.service = None
        self.credentials = None
        self.root_folder_id = None

    def authenticate(self):
        """Handle the OAuth flow and return True if successful."""
        print(f"{Color.DARK_CYAN}Initializing Google Drive authentication...{Color.END}")
        
        creds = None
        token_file = self.config.get('token_file', 'token.json')
        secrets_file = self.config.get('client_secrets_file', 'client_secrets.json')

        if not os.path.exists(secrets_file):
            print(f"{Color.RED}Error: {secrets_file} not found. Please configure OAuth credentials.{Color.END}")
            return False

        if os.path.exists(token_file):
            try:
                creds = Credentials.from_authorized_user_file(token_file, self.SCOPES)
            except Exception as e:
                print(f"{Color.YELLOW}Error reading token file: {e}{Color.END}")

        if not creds or not creds.valid:
            if creds and creds.expired and creds.refresh_token:
                print(f"{Color.DARK_CYAN}Refreshing expired token...{Color.END}")
                try:
                    creds.refresh(Request())
                except Exception as e:
                    print(f"{Color.YELLOW}Token refresh failed: {e}. Initiating new authentication...{Color.END}")
                    creds = None
            
            if not creds:
                try:
                    flow = InstalledAppFlow.from_client_secrets_file(secrets_file, self.SCOPES)
                    print(f"{Color.DARK_CYAN}Please login in your browser...{Color.END}")
                    creds = flow.run_local_server(port=0, success_message=SUCCESS_PAGE)
                except Exception as e:
                    print(f"{Color.RED}Authentication failed: {e}{Color.END}")
                    return False

            with open(token_file, 'w') as token:
                token.write(creds.to_json())
                print(f"{Color.GREEN}Token saved to {token_file}{Color.END}")

        try:
            self.service = build('drive', 'v3', credentials=creds)
            self.credentials = creds
            
            # Get user email
            user_info = self.service.about().get(fields="user").execute()
            email = user_info['user']['emailAddress']
            print(f"{Color.GREEN}Successfully authenticated as {email}{Color.END}")
            
            return True
        except Exception as e:
            print(f"{Color.RED}Failed to initialize Drive service: {e}{Color.END}")
            return False

    def _handle_upload_with_refresh(self, request):
        """Execute request with token refresh handling."""
        try:
            return request.execute()
        except HttpError as e:
            if e.resp.status in [401, 403]:
                if self.credentials.refresh_token:
                    print(f"{Color.YELLOW}Token expired, refreshing...{Color.END}")
                    self.credentials.refresh(Request())
                    return self._handle_upload_with_refresh(request)
                else:
                    print(f"{Color.YELLOW}Token refresh failed, re-authenticating...{Color.END}")
                    if self.authenticate():
                        return self._handle_upload_with_refresh(request)
            raise

    @staticmethod
    def _escape_query_value(value):
        """Escape a literal for use inside a Drive query string ('...')."""
        return value.replace("\\", "\\\\").replace("'", "\\'")

    def file_exists(self, folder_path, file_name):
        """Return True if a file with this exact name exists (untrashed) under the
           given folder path. Uses an exact name= match scoped to the parent folder
           rather than a fullText search, which gave false negatives when the name
           (or an id within it) also appeared inside other files' content. Handles
           duplicate folders by searching every matching branch."""
        print(f"Checking for file {file_name} in folder {folder_path}")

        # Resolve the folder path, collecting ALL folders that match at each level
        # (there may be duplicates created by earlier runs).
        parent_ids = [self.root_folder_id] if self.root_folder_id else [None]
        for folder in folder_path.split(os.sep):
            if not folder:
                continue
            safe_folder = self._escape_query_value(folder)
            next_ids = []
            for parent_id in parent_ids:
                query = (
                    f"name = '{safe_folder}' "
                    f"and mimeType = 'application/vnd.google-apps.folder' "
                    f"and trashed = false"
                )
                if parent_id:
                    query += f" and '{parent_id}' in parents"
                results = self.service.files().list(
                    q=query, spaces='drive', fields='files(id)'
                ).execute()
                next_ids.extend(f['id'] for f in results.get('files', []))
            if not next_ids:
                print(f"Found file: False (folder '{folder}' not found)")
                return False
            parent_ids = next_ids

        # Look for the exact file name in any of the resolved folders.
        safe_name = self._escape_query_value(file_name)
        for parent_id in parent_ids:
            query = f"name = '{safe_name}' and trashed = false and '{parent_id}' in parents"
            results = self.service.files().list(
                q=query, spaces='drive', fields='files(id, name)'
            ).execute()
            if results.get('files'):
                print("Found file: True")
                return True

        print("Found file: False")
        return False
        
    def create_folder(self, folder_name, parent_id=None):
        """Create a folder in Google Drive and return its ID."""
        file_metadata = {
            'name': folder_name,
            'mimeType': 'application/vnd.google-apps.folder'
        }
        if parent_id:
            file_metadata['parents'] = [parent_id]
        
        try:
            folder = self._handle_upload_with_refresh(
                self.service.files().create(body=file_metadata, fields='id')
            )
            return folder.get('id')
        except Exception as e:
            print(f"{Color.RED}Failed to create folder {folder_name}: {str(e)}{Color.END}")
            return None

    def get_or_create_folder_path(self, folder_path, parent_id=None):
        """Navigate or create folder structure in Google Drive."""
        current_parent = parent_id
        for folder in folder_path.split(os.sep):
            if not folder:
                continue
            
            query = f"name='{folder}' and mimeType='application/vnd.google-apps.folder'"
            if current_parent:
                query += f" and '{current_parent}' in parents"
            
            try:
                results = self._handle_upload_with_refresh(
                    self.service.files().list(
                        q=query,
                        spaces='drive',
                        fields='files(id)'
                    )
                )
                
                if results.get('files'):
                    current_parent = results['files'][0]['id']
                    print("Found existing folder %s" % (folder_path))
                else:
                    current_parent = self.create_folder(folder, current_parent)
                    print("Created a new folder %s" % (folder_path))
                    if not current_parent:
                        return None
            except Exception as e:
                print(f"{Color.RED}Failed to navigate folders: {str(e)}{Color.END}")
                return None
        
        return current_parent

    def upload_file(self, local_path, folder_name, filename):
        """Upload file to Google Drive with retry logic."""
        try:
            folder_id = self.get_or_create_folder_path(folder_name, self.root_folder_id)
            if not folder_id:
                return False

            file_metadata = {
                'name': filename,
                'parents': [folder_id]
            }
            
            media = MediaFileUpload(
                local_path,
                resumable=True
            )

            max_retries = int(self.config.get('max_retries', 3))
            retry_delay = int(self.config.get('retry_delay', 5))
            failed_log = self.config.get('failed_log', 'failed-uploads.log')

            for attempt in range(max_retries):
                try:
                    print(f"    Attempt {attempt + 1} of {max_retries}...")
                    request = self.service.files().create(
                        body=file_metadata,
                        media_body=media,
                        fields='id'
                    )
                    self._handle_upload_with_refresh(request)
                    print(f"    {Color.GREEN}Success!{Color.END}")
                    return True
                except Exception as e:
                    if attempt < max_retries - 1:
                        print(f"    {Color.YELLOW}Retry after {retry_delay} seconds...{Color.END}")
                        import time
                        time.sleep(retry_delay)
                    else:
                        print(f"{Color.RED}Upload failed: {str(e)}{Color.END}")
                        with open(failed_log, 'a') as log:
                            log.write(f"{datetime.now()}: Failed to upload {filename} - {str(e)}\n")
                        return False
        except Exception as e:
            print(f"{Color.RED}Upload preparation failed: {str(e)}{Color.END}")
            return False

    def initialize_root_folder(self):
        """Create root folder with timestamp."""
        timestamp = datetime.now().strftime("%Y-%m-%d-%H%M%S")
        # root_folder_name = f"{self.config.get('root_folder_name', 'zoom-recording-downloader')}-{timestamp}"
        root_folder_name = f"{self.config.get('root_folder_name', 'zoom-recording-downloader')}"
        # self.root_folder_id = self.create_folder(root_folder_name)
        self.root_folder_id = self.get_or_create_folder_path(root_folder_name)
        return self.root_folder_id is not None