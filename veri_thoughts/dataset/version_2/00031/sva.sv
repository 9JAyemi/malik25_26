module Mealy_sva (
    input logic       in,
    input logic       out,
    input logic [1:0] state
);

    localparam logic [1:0] s0 = 2'd0;
    localparam logic [1:0] s1 = 2'd1;
    localparam logic [1:0] s2 = 2'd2;
    localparam logic [1:0] s3 = 2'd3;

    // Low out is absorbing and drives the state back to s0.
    check_low_out_sticks_and_resets_state: assert property (
        @(posedge in) !out |=> (!out && (state == s0))
    );

    // From s0 with out high, the next sampled state is s0 with out low.
    check_s0_drops_out_and_resets_state: assert property (
        @(posedge in) (out && (state == s0)) |=> (!out && (state == s0))
    );

    // From s3 with out high, the next sampled state is s0 with out low.
    check_s3_drops_out_and_resets_state: assert property (
        @(posedge in) (out && (state == s3)) |=> (!out && (state == s0))
    );

    // From s1 with out high, one input edge later the machine is in s3 and out stays high.
    check_s1_steps_to_s3_with_out_high: assert property (
        @(posedge in) disable iff (!out) (out && (state == s1)) |=> (out && (state == s3))
    );

    // From s2 with out high, one input edge later the machine is in s0 and out stays high.
    check_s2_steps_to_s0_with_out_high: assert property (
        @(posedge in) disable iff (!out) (out && (state == s2)) |=> (out && (state == s0))
    );

    // From s1 with out high, the machine reaches low out and s0 within two input edges.
    check_s1_reaches_low_out_in_two_edges: assert property (
        @(posedge in) (out && (state == s1)) |=> (out && (state == s3)) ##1 (!out && (state == s0))
    );

    // From s2 with out high, the machine reaches low out and s0 within two input edges.
    check_s2_reaches_low_out_in_two_edges: assert property (
        @(posedge in) (out && (state == s2)) |=> (out && (state == s0)) ##1 (!out && (state == s0))
    );

endmodule