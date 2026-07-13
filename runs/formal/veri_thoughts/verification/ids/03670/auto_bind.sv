// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, F_add, d32, F_sub, d34, F_and, d36, F_or, d37, F_slt, d42, ALU_add, b010, ALU_sub, b110, ALU_and, b000, ALU_or, b001, ALU_slt, b111, check_aluop_00_maps_to_add, assert, property, posedge, b00, check_aluop_01_maps_to_sub, b01, check_rtype_add_maps_to_add, b10, check_rtype_sub_maps_to_sub, check_rtype_and_maps_to_and, check_rtype_or_maps_to_or, check_rtype_slt_maps_to_slt
bind alu_ctl alu_ctl_sva auto_sva_inst (
    .ALUOp(ALUOp),
    .Funct(Funct),
    .ALUOperation(ALUOperation)
);
