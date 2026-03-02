// Types for the example
interface Auth {
  workspaceId: string;
  userId: string;
}

interface DbQuery {
  where: { workspaceId: string };
}

declare function dbProjectsFindMany(query: DbQuery): Promise<any[]>;
declare function dbTasksFindMany(query: DbQuery): Promise<any[]>;

// @requires auth.workspaceId > 0
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant read-only: ¬ ∃ call db.*.update
// @invariant read-only: ¬ ∃ call db.*.create
// @invariant read-only: ¬ ∃ call db.*.delete
async function exportWorkspaceData(auth: Auth, format: string) {
  const projects = await dbProjectsFindMany({
    where: { workspaceId: auth.workspaceId },
  });

  const tasks = await dbTasksFindMany({
    where: { workspaceId: auth.workspaceId },
  });

  return { projects, tasks };
}
