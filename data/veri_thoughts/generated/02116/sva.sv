module MUX4to1_using_2to1_sva (
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic S0,
    input logic S1,
    input logic Y
);
    // Y implements 4:1 mux function built from nested 2:1 muxes.
    check_mux_function_direct: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            Y == ((S1 == 1'b0) ? ((S0 == 1'b0) ? D0 : D1) : ((S0 == 1'b0) ? D2 : D3))
    );

    // When S1=0 and S0=0, output equals D0.
    check_decode_s1_0_s0_0: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (!S1 && !S0) |-> (Y == D0)
    );

    // When S1=0 and S0=1, output equals D1.
    check_decode_s1_0_s0_1: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (!S1 && S0) |-> (Y == D1)
    );

    // When S1=1 and S0=0, output equals D2.
    check_decode_s1_1_s0_0: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (S1 && !S0) |-> (Y == D2)
    );

    // When S1=1 and S0=1, output equals D3.
    check_decode_s1_1_s0_1: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (S1 && S0) |-> (Y == D3)
    );

    // If D0==D1 and S1=0, S0 has no effect and Y equals D0.
    check_group0_data_equality_bypasses_s0: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (!S1 && (D0 == D1)) |-> (Y == D0)
    );

    // If D2==D3 and S1=1, S0 has no effect and Y equals D2.
    check_group1_data_equality_bypasses_s0: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (S1 && (D2 == D3)) |-> (Y == D2)
    );

    // If all data inputs are equal, Y equals that common value.
    check_all_data_equal_constant_output: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            ((D0 == D1) && (D1 == D2) && (D2 == D3)) |-> (Y == D0)
    );

    // With S0=0, Y selects between D0 and D2 by S1.
    check_s0_low_path: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (!S0) |-> (Y == ((S1 == 1'b0) ? D0 : D2))
    );

    // With S0=1, Y selects between D1 and D3 by S1.
    check_s0_high_path: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (S0) |-> (Y == ((S1 == 1'b0) ? D1 : D3))
    );

    // With S1=0, Y selects between D0 and D1 by S0.
    check_s1_low_path: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (!S1) |-> (Y == ((S0 == 1'b0) ? D0 : D1))
    );

    // With S1=1, Y selects between D2 and D3 by S0.
    check_s1_high_path: assert property (
        @(posedge D0 or negedge D0 or posedge D1 or negedge D1 or posedge D2 or negedge D2 or posedge D3 or negedge D3 or posedge S0 or negedge S0 or posedge S1 or negedge S1)
            (S1) |-> (Y == ((S0 == 1'b0) ? D2 : D3))
    );
endmodule