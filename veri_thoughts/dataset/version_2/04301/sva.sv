module velocityControlHdl_Dynamic_Saturation_block1_sva (
    input  logic               clk,
    input  logic signed [17:0] up,
    input  logic signed [35:0] u,
    input  logic signed [17:0] lo,
    input  logic signed [35:0] y,
    input  logic               sat_mode
);

    wire signed [35:0] up_dtc;
    wire signed [35:0] lo_dtc;
    wire               LowerRelop1_relop1;
    wire               UpperRelop_relop1;
    wire signed [35:0] Switch_out1;
    wire signed [35:0] Switch2_out1;
    wire               LowerRelop1_out1;

    assign up_dtc            = {{11{up[17]}}, {up, 7'b0000000}};
    assign lo_dtc            = {{11{lo[17]}}, {lo, 7'b0000000}};
    assign LowerRelop1_relop1 = (u > up_dtc ? 1'b1 : 1'b0);
    assign UpperRelop_relop1  = (u < lo_dtc ? 1'b1 : 1'b0);
    assign Switch_out1        = (UpperRelop_relop1 == 1'b0 ? u : lo_dtc);
    assign Switch2_out1       = (LowerRelop1_relop1 == 1'b0 ? Switch_out1 : up_dtc);
    assign LowerRelop1_out1   = LowerRelop1_relop1 | UpperRelop_relop1;

    // y follows the RTL's two-stage saturation mux chain.
    check_y_matches_switch_chain: assert property (
        @(posedge clk) y == Switch2_out1
    );

    // sat_mode is the OR of the upper and lower limit compares.
    check_sat_mode_matches_compare_or: assert property (
        @(posedge clk) sat_mode == LowerRelop1_out1
    );

    // If u exceeds the upper limit, y clamps to the upper value.
    check_upper_limit_clamps_output: assert property (
        @(posedge clk) LowerRelop1_relop1 |-> (y == up_dtc)
    );

    // If only the lower limit compare hits, y clamps to the lower value.
    check_lower_limit_clamps_output: assert property (
        @(posedge clk) (!LowerRelop1_relop1 && UpperRelop_relop1) |-> (y == lo_dtc)
    );

    // If neither compare hits, u passes through and sat_mode stays low.
    check_in_range_passthrough: assert property (
        @(posedge clk) (!LowerRelop1_relop1 && !UpperRelop_relop1) |-> ((y == u) && (sat_mode == 1'b0))
    );

    // If both compares hit, the second switch gives upper clamp priority.
    check_overlap_prefers_upper_limit: assert property (
        @(posedge clk) (LowerRelop1_relop1 && UpperRelop_relop1) |-> ((y == up_dtc) && (sat_mode == 1'b1))
    );

    // Equality at the upper limit is not an upper saturation if the lower compare is clear.
    check_upper_boundary_no_saturation: assert property (
        @(posedge clk) ((u == up_dtc) && !UpperRelop_relop1) |-> ((y == u) && (sat_mode == 1'b0))
    );

    // Equality at the lower limit is not a lower saturation if the upper compare is clear.
    check_lower_boundary_no_saturation: assert property (
        @(posedge clk) ((u == lo_dtc) && !LowerRelop1_relop1) |-> ((y == u) && (sat_mode == 1'b0))
    );

endmodule