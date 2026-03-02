interface Auth {
  workspaceId: string;
  userId: string;
}

declare const db: {
  apiKey: {
    findUnique(query: {
      where: { id: string; workspaceId: string };
    }): Promise<{ id: string; key: string }>;
    update(query: {
      where: { id: string };
      data: { key: string };
    }): Promise<void>;
  };
};

declare function generateKey(): Promise<string>;

declare const logger: {
  info(msg: string): Promise<void>;
};

// @requires auth.workspaceId > 0
// @invariant no-secret-leak: ¬ tainted apiKey in call logger.*
async function rotateApiKey(auth: Auth, keyId: string) {
  const existing = await db.apiKey.findUnique({
    where: { id: keyId, workspaceId: auth.workspaceId },
  });

  const apiKey = existing.key;
  const newKey = await generateKey();

  await db.apiKey.update({
    where: { id: keyId },
    data: { key: newKey },
  });

  await logger.info("API key rotated successfully");
}
