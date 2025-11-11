from e3.auth.gitlab import gen_gitlab_token
import gitlab
import os

# This script assumes that another project (hardcoded here as
# "eng/spark/spark2014") has a submodule pointing to our project. The purpose
# of this script is to create a merge request in that other project, that
# updates the submodule information to the current commit SHA.

base_url = os.environ["CI_SERVER_URL"]
project_name = "eng/spark/spark2014"
target_commit = os.environ["CI_COMMIT_SHORT_SHA"]
target_commit_long = os.environ["CI_COMMIT_SHA"]
target_branch = os.environ["CI_COMMIT_REF_NAME"]
commit_message = "Automatic submodule commit"
mr_title = "Automatic submodule commit"
mr_body = "no-issue-check"


def main():

    gl = gitlab.Gitlab(base_url, private_token=gen_gitlab_token()["token"])
    project = gl.projects.get(project_name)
    mr_branch = f"automated-submodule-update-{target_commit}"
    project.branches.create({"branch": mr_branch, "ref": target_branch})
    project.update_submodule(
        "why3", mr_branch, target_commit_long, commit_message=commit_message
    )
    mr = project.mergerequests.create(
        {
            "source_branch": mr_branch,
            "target_branch": target_branch,
            "title": mr_title,
            "description": mr_body,
        }
    )
    print(f"Merge request created: {mr.web_url}")


if __name__ == "__main__":
    main()
