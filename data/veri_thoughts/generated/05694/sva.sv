module boolean_ops_sva (
    input logic        clk,
    input logic [63:0] rs1_data,
    input logic [63:0] rs2_data,
    input logic        isand,
    input logic        isor,
    input logic        isxor,
    input logic        pass_rs2_data,
    input logic        inv_logic,
    input logic        ifu_exu_sethi_inst_e,
    input logic [63:0] logic_out
);

    // logic_out must match the implemented priority mux and datapath.
    check_logic_out_mux_function: assert property (
        @(posedge clk)
        logic_out == (
            isand ? (rs1_data & (rs2_data ^ {64{inv_logic}})) :
            isor  ? (rs1_data | (rs2_data ^ {64{inv_logic}})) :
            isxor ? (rs1_data ^ (rs2_data ^ {64{inv_logic}})) :
                    {(rs2_data[63:32] & {32{~ifu_exu_sethi_inst_e}}), rs2_data[31:0]}
        )
    );

    // isand selects the AND path regardless of other select inputs.
    check_and_selected: assert property (
        @(posedge clk)
        isand |-> (logic_out == (rs1_data & (rs2_data ^ {64{inv_logic}})))
    );

    // isor selects the OR path when isand is not asserted.
    check_or_selected: assert property (
        @(posedge clk)
        (!isand && isor) |-> (logic_out == (rs1_data | (rs2_data ^ {64{inv_logic}})))
    );

    // isxor selects the XOR path when higher-priority selects are not asserted.
    check_xor_selected: assert property (
        @(posedge clk)
        (!isand && !isor && isxor) |-> (logic_out == (rs1_data ^ (rs2_data ^ {64{inv_logic}})))
    );

    // With no boolean select asserted, logic_out must follow mov_data.
    check_mov_selected: assert property (
        @(posedge clk)
        (!isand && !isor && !isxor) |-> (
            logic_out == {(rs2_data[63:32] & {32{~ifu_exu_sethi_inst_e}}), rs2_data[31:0]}
        )
    );

    // In mov mode, the upper half is masked off only by ifu_exu_sethi_inst_e.
    check_mov_upper_half_masked: assert property (
        @(posedge clk)
        (!isand && !isor && !isxor) |-> (
            logic_out[63:32] == (rs2_data[63:32] & {32{~ifu_exu_sethi_inst_e}})
        )
    );

    // In mov mode, the lower half always passes rs2_data unchanged.
    check_mov_lower_half_passes_rs2: assert property (
        @(posedge clk)
        (!isand && !isor && !isxor) |-> (logic_out[31:0] == rs2_data[31:0])
    );

endmodule