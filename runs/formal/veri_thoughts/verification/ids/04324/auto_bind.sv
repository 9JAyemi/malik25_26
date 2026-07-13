// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): ALU_OP_ADD, b0000, ALU_OP_SUB, b0001, ALU_OP_ADC, b0010, ALU_OP_SBC, b0011, ALU_OP_AND, b0100, ALU_OP_OR, b0101, ALU_OP_NOT, b0110, ALU_OP_XOR, b0111, ALU_OP_SHL, b1000, ALU_OP_SHR, b1001, ALU_OP_SAL, b1010, ALU_OP_SAR, b1011, ALU_OP_ROL, b1100, ALU_OP_ROR, b1101, ALU_OP_RCL, b1110, ALU_OP_RCR, b1111, function, automatic, expected_outputs, op, cf_in, t, begin, case, b0000000, b0, default, h000, endcase, h00, end, endfunction, check_zero_flag_matches_result, assert, property, posedge, b1, check_sign_flag_matches_result, check_add_outputs, past, check_sub_outputs, check_adc_outputs_use_prior_cf, check_sbc_outputs_use_prior_cf, check_and_outputs, check_or_outputs, check_not_outputs, check_xor_outputs, check_shl_outputs, check_shr_outputs, check_sal_outputs, check_sar_outputs, check_rol_outputs, check_ror_outputs, check_rcl_outputs_use_prior_cf, check_rcr_outputs_use_prior_cf
bind alu alu_sva auto_sva_inst (
    .clk(clk),
    .A(A),
    .B(B),
    .operation(operation),
    .result(result),
    .CF(CF),
    .ZF(ZF),
    .SF(SF),
    .a(A),
    .b(B)
);
