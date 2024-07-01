import re

def merge_v_from_ab(name: str, descr: str):
    print(f"{name}: {descr}:")
    print("\tv0=...")
    p=re.compile('v=\[(.*)\]')
    m=p.match(descr)
    list=m.group(1).split(',')
    p=re.compile('([ab])(\d+)')
    for i, e in enumerate(list):
        tab, j = p.match(e).groups()
        print(f'\tv{i+1} = (store v{i} {i} (select {tab} {j}))')
    
def transpose_v_from_a(n: int):
    print(f'transpose {n}x{n}:')
    print("\tv0=...")
    for i in range(n):
        for j in range(n):
            ij=i*n+j
            ji=j*n+i
            print(f'\tv{ij+1} = (store v{ij} {ij} (select a {ji}))')

def mm256_shuffle_ps(t: list):
    assert(len(t)==4)
    return merge_v_from_ab(name=f'merge_v_from_ab({t})', descr=f'v=[a{t[3]},a{t[2]},b{t[1]},b{t[0]},a{t[3]+4},a{t[2]+4},b{t[1]+4},b{t[0]+4}]')

def mm256_permut2f128_ps(t: list):
    assert(len(t)==4)


def main():
    mm256_shuffle_ps([1,0,1,0])
    mm256_unpacklo_ps = merge_v_from_ab(name="mm256_unpacklo_ps", descr="v=[a0,b0,a1,b1,a4,b4,a5,b5]")
    mm256_unpackhi_ps = merge_v_from_ab(name="mm256_unpackhi_ps", descr="v=[a2,b2,a3,b3,a6,b6,a7,b7]")
    transpose_v_from_a(8)
    return 0

if __name__ == '__main__':
    main()  