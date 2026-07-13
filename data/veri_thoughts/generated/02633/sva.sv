module AO222EHD_sva (
    input logic out,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic e,
    input logic f
);
    // Combinational logic; no clock/reset in DUT. Sample on any input edge.

    // Output equals (a & b) | (c & d) | (e & f) at all times.
    check_functional_equivalence: assert property (
        @(posedge a or negedge a or
          posedge b or negedge b or
          posedge c or negedge c or
          posedge d or negedge d or
          posedge e or negedge e or
          posedge f or negedge f)
        (out === ((a & b) | (c & d) | (e & f)))
    );

    // If a&b is 1, out must be 1 in the same cycle.
    check_ab_forces_out: assert property (
        @(posedge a or negedge a or
          posedge b or negedge b or
          posedge c or negedge c or
          posedge d or negedge d or
          posedge e or negedge e or
          posedge f or negedge f)
        ((a & b) == 1'b1) |-> (out == 1'b1)
    );

    // If no pair is 1, out must be 0 in the same cycle.
    check_no_pair_forces_out_low: assert property (
        @(posedge a or negedge a or
          posedge b or negedge b or
          posedge c or negedge c or
          posedge d or negedge d or
          posedge e or negedge e or
          posedge f or negedge f)
        (((a & b) | (c & d) | (e & f)) == 1'b0) |-> (out == 1'b0)
    );

endmodule