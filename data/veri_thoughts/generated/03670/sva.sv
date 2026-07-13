module alu_ctl_sva (
    input logic        clk,
    input logic [1:0]  ALUOp,
    input logic [5:0]  Funct,
    input logic [2:0]  ALUOperation
);

    localparam [5:0] F_add = 6'd32;
    localparam [5:0] F_sub = 6'd34;
    localparam [5:0] F_and = 6'd36;
    localparam [5:0] F_or  = 6'd37;
    localparam [5:0] F_slt = 6'd42;

    localparam [2:0] ALU_add = 3'b010;
    localparam [2:0] ALU_sub = 3'b110;
    localparam [2:0] ALU_and = 3'b000;
    localparam [2:0] ALU_or  = 3'b001;
    localparam [2:0] ALU_slt = 3'b111;

    // ALUOp 00 selects the add operation.
    check_aluop_00_maps_to_add: assert property (
        @(posedge clk) (ALUOp == 2'b00) |-> (ALUOperation == ALU_add)
    );

    // ALUOp 01 selects the subtract operation.
    check_aluop_01_maps_to_sub: assert property (
        @(posedge clk) (ALUOp == 2'b01) |-> (ALUOperation == ALU_sub)
    );

    // R-type add funct selects the add operation.
    check_rtype_add_maps_to_add: assert property (
        @(posedge clk) ((ALUOp == 2'b10) && (Funct == F_add)) |-> (ALUOperation == ALU_add)
    );

    // R-type sub funct selects the subtract operation.
    check_rtype_sub_maps_to_sub: assert property (
        @(posedge clk) ((ALUOp == 2'b10) && (Funct == F_sub)) |-> (ALUOperation == ALU_sub)
    );

    // R-type and funct selects the and operation.
    check_rtype_and_maps_to_and: assert property (
        @(posedge clk) ((ALUOp == 2'b10) && (Funct == F_and)) |-> (ALUOperation == ALU_and)
    );

    // R-type or funct selects the or operation.
    check_rtype_or_maps_to_or: assert property (
        @(posedge clk) ((ALUOp == 2'b10) && (Funct == F_or)) |-> (ALUOperation == ALU_or)
    );

    // R-type slt funct selects the set-less-than operation.
    check_rtype_slt_maps_to_slt: assert property (
        @(posedge clk) ((ALUOp == 2'b10) && (Funct == F_slt)) |-> (ALUOperation == ALU_slt)
    );

endmodule