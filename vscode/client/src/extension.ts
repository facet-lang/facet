import { workspace, ExtensionContext } from 'vscode';

import {
	Executable,
	LanguageClient,
	LanguageClientOptions,
	ServerOptions
} from 'vscode-languageclient';

let client: LanguageClient;

export function activate(context: ExtensionContext) {
	let server: Executable = {
		command: "cabal",
		args: ["run", "facetc", "--", "lsp", "--path", "/Users/rob/Projects/facet/facetc/out.log"],
		options: {
			cwd: "/Users/rob/Projects/facet"
		}
	};

	let serverOptions: ServerOptions = server;

	let clientOptions: LanguageClientOptions = {
		documentSelector: [{ scheme: 'file', language: 'facet' }],
		synchronize: {
			fileEvents: workspace.createFileSystemWatcher('**/*.facet')
		}
	};

	client = new LanguageClient(
		'facetServer',
		'Facet language server',
		serverOptions,
		clientOptions
	);

	client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
