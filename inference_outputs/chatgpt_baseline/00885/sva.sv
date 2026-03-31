module chacha_qr_sva (
    input  logic        CLK,       // verification clock (DUT is combinational)
    input  logic        RESETn,    // active-low reset for property disable (no reset in DUT)
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic [31:0] c,
    input  logic [31:0] d,
    input  logic [31:0] a_prim,
    input  logic [31:0] b_prim,
    input  logic [31:0] c_prim,
    input  logic [31:0] d_prim
);
    // Rotate-left helper functions matching RTL slices.
    function automatic [31:0] rol16(input [31:0] x); rol16 = {x[15:0], x[31:16]}; endfunction
    function automatic [31:0] rol12(input [31:0] x); rol12 = {x[19:0], x[31:20]}; endfunction
    function automatic [31:0] rol8 (input [31:0] x); rol8  = {x[23:0], x[31:24]}; endfunction
    function automatic [31:0] rol7 (input [31:0] x); rol7  = {x[24:0], x[31:25]}; endfunction

    // Reference computation mirroring the combinational RTL.
    logic [31:0] a0_e, a1_e;
    logic [31:0] b0_e, b1_e, b2_e, b3_e;
    logic [31:0] c0_e, c1_e;
    logic [31:0] d0_e, d1_e, d2_e, d3_e;

    assign a0_e = a + b;
    assign d0_e = d ^ a0_e;
    assign d1_e = rol16(d0_e);
    assign c0_e = c + d1_e;
    assign b0_e = b ^ c0_e;
    assign b1_e = rol12(b0_e);
    assign a1_e = a0_e + b1_e;
    assign d2_e = d1_e ^ a1_e;
    assign d3_e = rol8(d2_e);
    assign c1_e = c0_e + d3_e;
    assign b2_e = b1_e ^ c1_e;
    assign b3_e = rol7(b2_e);

    ///// Functional correctness against the RTL computation /////
    // a_prim must equal a1_e = (a + b) + rol12(b ^ (c + rol16(d ^ (a + b)))).
    check_a_prim_matches_reference: assert property (
        @(posedge CLK) disable iff (!RESETn) a_prim == a1_e
    );
    // b_prim must equal b3_e = rol7( rol12(b ^ (c + rol16(d ^ (a + b)))) ^ c1_e ).
    check_b_prim_matches_reference: assert property (
        @(posedge CLK) disable iff (!RESETn) b_prim == b3_e
    );
    // c_prim must equal c1_e = (c + rol16(d ^ (a + b))) + d_prim.
    check_c_prim_matches_reference: assert property (
        @(posedge CLK) disable iff (!RESETn) c_prim == c1_e
    );
    // d_prim must equal d3_e = rol8( rol16(d ^ (a + b)) ^ a_prim ).
    check_d_prim_matches_reference: assert property (
        @(posedge CLK) disable iff (!RESETn) d_prim == d3_e
    );

    ///// Closed-form relations directly from inputs /////
    // a_prim equals (a + b) + rol12(b ^ (c + rol16(d ^ (a + b)))).
    check_a_prim_closed_form: assert property (
        @(posedge CLK) disable iff (!RESETn)
            a_prim == (a + b) + rol12(b ^ (c + rol16(d ^ (a + b))))
    );
    // d_prim equals rol8( rol16(d ^ (a + b)) ^ ((a + b) + rol12(b ^ (c + rol16(d ^ (a + b))))) ).
    check_d_prim_closed_form: assert property (
        @(posedge CLK) disable iff (!RESETn)
            d_prim == rol8( rol16(d ^ (a + b)) ^ ((a + b) + rol12(b ^ (c + rol16(d ^ (a + b))))) )
    );
    // c_prim equals (c + rol16(d ^ (a + b))) + d_prim.
    check_c_prim_closed_form: assert property (
        @(posedge CLK) disable iff (!RESETn)
            c_prim == (c + rol16(d ^ (a + b))) + d_prim
    );
    // b_prim equals rol7( rol12(b ^ (c + rol16(d ^ (a + b)))) ^ c_prim ).
    check_b_prim_closed_form: assert property (
        @(posedge CLK) disable iff (!RESETn)
            b_prim == rol7( rol12(b ^ (c + rol16(d ^ (a + b)))) ^ c_prim )
    );

    ///// Combinational stability /////
    // If inputs are stable from the previous cycle, outputs must also be stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable({a, b, c, d}) |-> $stable({a_prim, b_prim, c_prim, d_prim})
    );
endmodule