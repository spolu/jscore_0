interface Auth {
  workspaceId: string;
  userId: string;
}

declare function dbTaskUpdate(query: {
  where: { id: string; projectId: string };
  data: { position: number };
}): Promise<void>;

// @requires auth.workspaceId > 0
// @invariant ws-isolation: ∀ call db.* (c) => c.where.projectId = projectId
async function reorderTasks(
  auth: Auth,
  projectId: string,
  tasks: string[]
) {
  for (const taskId of tasks) {
    await dbTaskUpdate({
      where: { id: taskId, projectId: projectId },
      data: { position: 0 },
    });
  }
}
