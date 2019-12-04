prog_unsafe_r1_collide = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
moveTo(150, 200, 0, 1);
"""

prog_safe_r1_set = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
"""

prog_safe_r1_set_rev = """moveTo(150, 100, 0, 2);
moveTo(100, 150, 0, 1);
"""

prog_safe_longer = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
moveTo(100, 160, 0, 2);
moveTo(100, 170, 0, 2);
moveTo(50, 100, 0, 1);
moveTo(0, 0, 0, 1);
"""

prog_unsafe_longer = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
moveTo(100, 160, 0, 2);
moveTo(100, 170, 0, 2);
moveTo(50, 100, 0, 1);
moveTo(0, 0, 0, 1);
moveTo(101, 171, 0, 1);
"""
prog_unsafe_cross = """moveTo(300, 300, 0, 1);
moveTo(0, 300, 0, 2);
"""

prog_safe_sleep_before_collide = """moveTo(150, 100, 0, 1);
sleep(8, 2);
moveTo(100, 150, 0, 2);
moveTo(150, 200, 0, 1);
"""

prog_unsafe_not_enough_sleep_before_collide = """moveTo(150, 100, 0, 1);
sleep(7, 2);
moveTo(100, 150, 0, 2);
moveTo(150, 200, 0, 1);
"""

prog_safe_easy_optimize = """moveTo(0, 20, 0, 1);
moveTo(0, 100, 0, 1);
travel(300, 20, 0, 1);
moveTo(300, 100, 0, 1);
sleep(300, 2);
"""

prog_safe_easy_post_opt = """moveTo(0, 20, 0, 1);
moveTo(0, 100, 0, 1);
moveTo(300, 20, 0, 2);
moveTo(300, 100, 0, 2);
"""

