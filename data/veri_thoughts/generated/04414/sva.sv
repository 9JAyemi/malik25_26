module sparc_exu_aluspr_sva (
    input logic        clk,
    input logic [63:0] rs1_data,
    input logic [63:0] rs2_data,
    input logic        cin,
    input logic [63:0] spr_out
);

    // In add mode, spr_out must equal rs1_data plus rs2_data.
    check_add_mode_result: assert property (
        @(posedge clk) cin |-> (spr_out == (rs1_data + rs2_data))
    );

    // In subtract mode, spr_out must equal rs1_data minus rs2_data.
    check_sub_mode_result: assert property (
        @(posedge clk) !cin |-> (spr_out == (rs1_data - rs2_data))
    );

    // If all inputs are stable, the combinational output must stay stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) $stable({rs1_data, rs2_data, cin}) |-> $stable(spr_out)
    );

    // Subtracting equal operands must produce zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) (!cin && (rs1_data == rs2_data)) |-> (spr_out == 64'd0)
    );

    // In add mode, adding zero on rs2_data must pass rs1_data through.
    check_add_zero_right_identity: assert property (
        @(posedge clk) (cin && (rs2_data == 64'd0)) |-> (spr_out == rs1_data)
    );

    // In subtract mode, subtracting zero on rs2_data must pass rs1_data through.
    check_sub_zero_right_identity: assert property (
        @(posedge clk) (!cin && (rs2_data == 64'd0)) |-> (spr_out == rs1_data)
    );

endmodule