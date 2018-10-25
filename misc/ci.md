Continuous integration slaves are hosted on https://ci.inria.fr/ in the
`why3` project. They are of type `medium` (1 core at 2GHz and 2GB RAM)
with 40GB of storage.

:warning: Do not write any sensible information in this file, e.g., the CI token!

# To create a new slave

1.  create a virtual machine from the slave template
2.  connect to it by `ssh`
3.  run:
    ```
    hostname > /etc/hostname
    gitlab-runner register
    ```
4.  use the information from "CI/CD settings", `shell` for the type, and no tags
5.  enjoy

# To create the initial slave template (once in a while)

1.  create a virtual machine from a Debian 9 template
2.  connect to it by `ssh`
3.  run:
    ```
    apt-get update
    apt-get dist-upgrade
    apt-get install curl autoconf automake
    curl -L https://packages.gitlab.com/install/repositories/runner/gitlab-runner/script.deb.sh | bash
    curl -fsSL https://download.docker.com/linux/debian/gpg | apt-key add -
    apt-key fingerprint 0EBFCD88
    echo "deb https://download.docker.com/linux/debian stretch stable" >> /etc/apt/sources.list
    apt-get update
    apt-get install gitlab-runner docker-ce
    usermod -aG docker gitlab-runner
    apt-get clean
    ```
4.  remove any unneeded package coming from the original template
5.  stop the virtual machine
6.  take a snapshot of its storage volume
7.  turn the snapshot into a 64-bit Debian template
8.  restart the virtual machine
9.  turn the virtual machine into a proper slave (see above)

# To update the template (from time to time)

1.  create a virtual machine from the slave template
2.  connect to it by `ssh`
3.  run:
    ```
    apt-get update
    apt-get dist-upgrade
    apt-get clean
    ```
4.  finish as if creating the initial template (see above)

# To increase the storage space (if ever needed again)

1.  create a virtual machine from the slave template using a larger storage
2.  connect to it by `ssh`
3.  run:
    ```
    swapoff
    fdisk /dev/sda
    ```
4.  delete all the partitions
5.  create a primary partition that fills almost the whole volume except for 2GB (refuse to overwrite its signature)
6.  create a primary partition in the remaining space and turn its type to `82` (swap)
7.  write the partition to the disk and pray that you did not mess up
8.  reboot and reconnect to it by `ssh`
9.  run:
    ```
    resize2fs /dev/sda1
    mkswap /dev/sda2
    blkid
    ```
10. replace the `UUID` of `/dev/sda2` inside `/etc/fstab`
11. reboot
12. finish as if creating the initial template (see above)
