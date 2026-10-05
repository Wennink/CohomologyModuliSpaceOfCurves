
def get_marks_part(n, n_part):
    answer = []
    nr = 1
    for ni in n_part:
        answer += [nr] * ni
        nr += 1
    return tuple(answer)
