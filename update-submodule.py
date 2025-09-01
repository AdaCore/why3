from e3.auth.gitlab import gen_gitlab_token
import gitlab
import os
import subprocess

base_url = "https://" + os.environ['CI_SERVER_FQDN']
project_name = "eng/spark/spark2014"
target_commit = os.environ['CI_COMMIT_SHORT_SHA']
target_commit_long = os.environ['CI_COMMIT_SHA']
commit_message = "Automatic submodule commit"
mr_title = "Automatic submodule commit"
mr_body = "no-issue-check"

def main():

    gl = gitlab.Gitlab(base_url, private_token=gen_gitlab_token()["token"])
    project = gl.projects.get(project_name)
    master_branch = project.branches.get('master')
    mr_branch = f"automated-submodule-update-{target_commit}"
    project.branches.create({'branch' : mr_branch, 'ref' : master_branch.name})
    project.update_submodule("why3", mr_branch, target_commit_long, commit_message=commit_message)
    mr = project.mergerequests.create({
        'source_branch' : mr_branch,
        'target_branch' : master_branch.name,
        'title' : mr_title,
        'description' : mr_body
    })
    print(f'Merge request created: {mr.web_url}')


if __name__ == "__main__":
    main()
