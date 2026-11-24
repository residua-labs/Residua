/* timecell.c — KOKA-TABLE-1 timing cell. One command, one measurement.
 *
 * Usage: timecell <wall_seconds> -- <cmd> [args...]
 *
 * Fork+exec the command in its own process group; poll with
 * CLOCK_MONOTONIC; kill the group at the wall; wait4 for exit status and
 * rusage. Prints ONE TSV line to stdout:
 *
 *   wall_ns<TAB>maxrss_kb<TAB>cpu_us<TAB>status
 *
 * cpu_us is ru_utime + ru_stime in microseconds (the rule's "CPU seconds
 * beside the wall").
 * status: rc-<n> | signal-<n> | wall | spawnfail-<errno>
 * The child's stdout/stderr are inherited (the driver pipes them).
 * No dependencies beyond libc/POSIX: Linux ru_maxrss is KiB.
 * closure_claim = 0.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static long long now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (long long)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

int main(int argc, char **argv) {
  if (argc < 4 || strcmp(argv[2], "--") != 0) {
    fprintf(stderr, "usage: %s <wall_seconds> -- <cmd> [args...]\n", argv[0]);
    return 64;
  }
  double wall_s = strtod(argv[1], NULL);
  char **cmd = &argv[3];

  long long t0 = now_ns();
  pid_t pid = fork();
  if (pid < 0) {
    printf("0\t0\t0\tspawnfail-%d\n", errno);
    return 1;
  }
  if (pid == 0) {
    setpgid(0, 0);
    execvp(cmd[0], cmd);
    _exit(127);
  }

  int st = 0;
  struct rusage ru;
  memset(&ru, 0, sizeof ru);
  int walled = 0;
  for (;;) {
    /* wait4 WNOHANG both polls and, on reap, fills ru — the child must
       be reaped exactly once or rusage is lost. */
    pid_t r = wait4(pid, &st, WNOHANG, &ru);
    if (r == pid) break;
    if (r < 0) { if (errno == EINTR) continue; break; }
    if ((double)(now_ns() - t0) / 1e9 > wall_s) {
      walled = 1;
      kill(-pid, SIGKILL);
      wait4(pid, &st, 0, &ru);
      break;
    }
    usleep(2000);
  }
  long long wall_ns = now_ns() - t0;

  const char *status;
  char sbuf[32];
  if (walled) status = "wall";
  else if (WIFEXITED(st)) { snprintf(sbuf, sizeof sbuf, "rc-%d", WEXITSTATUS(st)); status = sbuf; }
  else if (WIFSIGNALED(st)) { snprintf(sbuf, sizeof sbuf, "signal-%d", WTERMSIG(st)); status = sbuf; }
  else status = "unknown";

  long long cpu_us = ru.ru_utime.tv_sec * 1000000LL + ru.ru_utime.tv_usec
                   + ru.ru_stime.tv_sec * 1000000LL + ru.ru_stime.tv_usec;

  printf("%lld\t%ld\t%lld\t%s\n", wall_ns, ru.ru_maxrss, cpu_us, status);
  return 0;
}
