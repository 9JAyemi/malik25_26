module MUX4_2to1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S1,
    input logic S0,
    input logic Z
);
    // NOTE: No clock/reset in RTL; pure combinational 4:1 MUX built from 2:1 gates.

    // Z equals full 4:1 mux function of A,B,C,D,S0,S1.
    check_mux_functional_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge S0 or negedge S0 or posedge S1 or negedge S1)
        (Z === (S1 ? (S0 ? D : C) : (S0 ? B : A)))
    );

    // When S1=0 and S0=0, Z equals A.
    check_sel_00_A: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge S0 or negedge S0 or posedge S1 or negedge S1)
        (S1 === 1'b0 && S0 === 1'b0) |=> (Z === A)
    );

    // When S1=0 and S0=1, Z equals B.
    check_sel_01_B: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge S0 or negedge S0 or posedge S1 or negedge S1)
        (S1 === 1'b0 && S0 === 1'b1) |=> (Z === B)
    );

    // When S1=1 and S0=0, Z equals C.
    check_sel_10_C: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge S0 or negedge S0 or posedge S1 or negedge S1)
        (S1 === 1'b1 && S0 === 1'b0) |=> (Z === C)
    );

    // When S1=1 and S0=1, Z equals D.
    check_sel_11_D: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge S0 or negedge S0 or posedge S1 or negedge S1)
        (S1 === 1'b1 && S0 === 1'b1) |=> (Z === D)
    );

    // When S1=0, Z equals 2:1 mux of A/B by S0.
    check_top_sel_low_path: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge S0 or negedge S0 or posedge S1 or negedge S1)
        (S1 === 1'b0) |=> (Z === (S0 ? B : A))
    );

    // When S1=1, Z equals 2:1 mux of C/D by S0.
    check_top_sel_high_path: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge S0 or negedge S0 or posedge S1 or negedge S1)
        (S1 === 1'b1) |=> (Z === (S0 ? D : C))
    );
endmodule