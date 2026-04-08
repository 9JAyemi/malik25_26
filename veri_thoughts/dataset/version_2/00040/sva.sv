module shift_register_sva (
    input logic Clock,
    input logic ALOAD,
    input logic [8:0] D,
    input logic SO,
    input logic [8:0] tmp,
    input logic n22
);

    // tmp[0] captures D[0] on each clock.
    check_tmp0_captures_d0: assert property (
        @(posedge Clock) !$initstate |-> (tmp[0] == $past(D[0]))
    );

    // tmp[1] shifts the previous tmp[0].
    check_tmp1_shifts_tmp0: assert property (
        @(posedge Clock) !$initstate |-> (tmp[1] == $past(tmp[0]))
    );

    // tmp[2] shifts the previous tmp[1].
    check_tmp2_shifts_tmp1: assert property (
        @(posedge Clock) !$initstate |-> (tmp[2] == $past(tmp[1]))
    );

    // tmp[3] shifts the previous tmp[2].
    check_tmp3_shifts_tmp2: assert property (
        @(posedge Clock) !$initstate |-> (tmp[3] == $past(tmp[2]))
    );

    // tmp[4] shifts the previous tmp[3].
    check_tmp4_shifts_tmp3: assert property (
        @(posedge Clock) !$initstate |-> (tmp[4] == $past(tmp[3]))
    );

    // tmp[5] shifts the previous tmp[4].
    check_tmp5_shifts_tmp4: assert property (
        @(posedge Clock) !$initstate |-> (tmp[5] == $past(tmp[4]))
    );

    // tmp[6] shifts the previous tmp[5].
    check_tmp6_shifts_tmp5: assert property (
        @(posedge Clock) !$initstate |-> (tmp[6] == $past(tmp[5]))
    );

    // tmp[7] shifts the previous tmp[6].
    check_tmp7_shifts_tmp6: assert property (
        @(posedge Clock) !$initstate |-> (tmp[7] == $past(tmp[6]))
    );

    // SO loads the previous D[0] when ALOAD was high.
    check_so_load_path: assert property (
        @(posedge Clock) (!$initstate && $past(ALOAD)) |-> (SO == $past(D[0]))
    );

    // SO shifts the previous tmp[1] when ALOAD was low.
    check_so_shift_path: assert property (
        @(posedge Clock) (!$initstate && !$past(ALOAD)) |-> (SO == $past(tmp[1]))
    );

    // n22 is always the AND of ALOAD and tmp[8].
    check_n22_and_decode: assert property (
        @(posedge Clock) (n22 == (ALOAD & tmp[8]))
    );

endmodule