# Ivy language server protocol implementation via pygls
from pygls.server import LanguageServer
from lsprotocol import types

server = LanguageServer('ivy-lsp-server', 'v0.1')

@server.feature(
    types.TEXT_DOCUMENT_COMPLETION
)

def completions(params:types.CompletionParams):
    document = server.workspace.get_document(params.text_document.uri)
    print('document: ', document)
    return []

def main():
    server.start_io()

if __name__=='__main__':
    main()