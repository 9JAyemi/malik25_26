module sky130_fd_sc_ms__o41ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    // Internal nets from RTL (bind hierarchically)
    input logic or0_out,
    input logic nand0_out_Y
);
    // Combinational cell; sample checks on any input edge.

    // OR stage equals OR of A1..A4.
    check_or_stage_function: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        or0_out == (A1 | A2 | A3 | A4)
    );

    // NAND stage equals ~(B1 & or0_out).
    check_nand_stage_function: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        nand0_out_Y == ~(B1 & or0_out)
    );

    // Buffer passes NAND stage to Y.
    check_buffer_passthrough: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        Y == nand0_out_Y
    );

    // Top-level function: Y == ~(B1 & (A1|A2|A3|A4)).
    check_top_function: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        Y == ~(B1 & (A1 | A2 | A3 | A4))
    );

    // B1 low forces Y high (NAND with 0).
    check_b1_low_forces_y_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // or0_out low forces Y high (NAND input 0).
    check_or0_low_forces_y_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        (or0_out == 1'b0) |-> (Y == 1'b1)
    );

    // B1 high makes Y the inversion of or0_out.
    check_b1_high_y_is_not_or0: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        (B1 == 1'b1) |-> (Y == ~or0_out)
    );

    // All A inputs low make or0_out low.
    check_all_a_low_or0_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0) && (A4 == 1'b0)) |-> (or0_out == 1'b0)
    );

    // Any single A high sets or0_out high.
    check_a1_high_sets_or: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        (A1 == 1'b1) |-> (or0_out == 1'b1)
    );
    check_a2_high_sets_or: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        (A2 == 1'b1) |-> (or0_out == 1'b1)
    );
    check_a3_high_sets_or: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        (A3 == 1'b1) |-> (or0_out == 1'b1)
    );
    check_a4_high_sets_or: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        (A4 == 1'b1) |-> (or0_out == 1'b1)
    );

    // Y low implies both B1 and or0_out are high (NAND characteristic).
    check_y_low_implies_inputs_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        (Y == 1'b0) |-> ((B1 == 1'b1) && (or0_out == 1'b1))
    );

    // Y high implies at least one NAND input is low.
    check_y_high_implies_some_input_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge A4 or negedge A4 or
          posedge B1 or negedge B1)
        (Y == 1'b1) |-> ((B1 == 1'b0) || (or0_out == 1'b0))
    );
endmodule