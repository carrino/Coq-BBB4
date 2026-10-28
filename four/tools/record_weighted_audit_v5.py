"""V5 direct replay with an exact-object full recursive audit receipt."""
import check_weighted_v5
import record_weighted_audit as recorded


def configure():
    recorded.producer = check_weighted_v5
    return recorded.configure()


if __name__ == '__main__':
    configure().main()
