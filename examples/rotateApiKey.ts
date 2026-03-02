interface Auth {
  workspaceId: string;
  userId: string;
}

declare function dbApiKeyFindUnique(query: {
  where: { id: string; workspaceId: string };
}): Promise<{ id: string; key: string }>;

declare function dbApiKeyUpdate(query: {
  where: { id: string };
  data: { key: string };
}): Promise<void>;

declare function generateKey(): Promise<string>;

declare function loggerInfo(msg: string): Promise<void>;

// @requires auth.workspaceId > 0
// @invariant no-secret-leak: ¬ tainted apiKey in call logger.*
async function rotateApiKey(auth: Auth, keyId: string) {
  const existing = await dbApiKeyFindUnique({
    where: { id: keyId, workspaceId: auth.workspaceId },
  });

  const apiKey = existing.key;
  const newKey = await generateKey();

  await dbApiKeyUpdate({
    where: { id: keyId },
    data: { key: newKey },
  });

  await loggerInfo("API key rotated successfully");
}
