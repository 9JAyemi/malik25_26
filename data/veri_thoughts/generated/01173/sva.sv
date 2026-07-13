module controlALU_sva (
    input logic [1:0] ALUop,
    input logic [5:0] instru,
    input logic clk,
    input logic [2:0] contALU
);
    // ALUop==00 forces contALU=010.
    check_map_aluop_00: assert property (
        @(posedge clk) (ALUop == 2'b00) |-> (contALU == 3'b010)
    );
    // ALUop==01 forces contALU=110.
    check_map_aluop_01: assert property (
        @(posedge clk) (ALUop == 2'b01) |-> (contALU == 3'b110)
    );
    // R-type: instru==100000 maps to 010 when ALUop!=00/01.
    check_map_rtype_add: assert property (
        @(posedge clk) ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b100000)) |-> (contALU == 3'b010)
    );
    // R-type: instru==100010 maps to 110 when ALUop!=00/01.
    check_map_rtype_sub: assert property (
        @(posedge clk) ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b100010)) |-> (contALU == 3'b110)
    );
    // R-type: instru==100100 maps to 000 when ALUop!=00/01.
    check_map_rtype_and: assert property (
        @(posedge clk) ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b100100)) |-> (contALU == 3'b000)
    );
    // R-type: instru==100101 maps to 001 when ALUop!=00/01.
    check_map_rtype_or: assert property (
        @(posedge clk) ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b100101)) |-> (contALU == 3'b001)
    );
    // R-type: instru==101010 maps to 111 when ALUop!=00/01.
    check_map_rtype_slt: assert property (
        @(posedge clk) ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b101010)) |-> (contALU == 3'b111)
    );
    // R-type default case maps to 101 when ALUop!=00/01 and instru not in known set.
    check_map_rtype_default: assert property (
        @(posedge clk) ((ALUop != 2'b00) && (ALUop != 2'b01) &&
                        (instru != 6'b100000) && (instru != 6'b100010) &&
                        (instru != 6'b100100) && (instru != 6'b100101) &&
                        (instru != 6'b101010)) |-> (contALU == 3'b101)
    );
    // Output 010 only when ALUop==00 or R-type add.
    check_inv_out_010: assert property (
        @(posedge clk) (contALU == 3'b010) |-> ((ALUop == 2'b00) ||
                                               ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b100000)))
    );
    // Output 110 only when ALUop==01 or R-type sub.
    check_inv_out_110: assert property (
        @(posedge clk) (contALU == 3'b110) |-> ((ALUop == 2'b01) ||
                                               ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b100010)))
    );
    // Output 000 only when R-type and instru==100100.
    check_inv_out_000: assert property (
        @(posedge clk) (contALU == 3'b000) |-> ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b100100))
    );
    // Output 001 only when R-type and instru==100101.
    check_inv_out_001: assert property (
        @(posedge clk) (contALU == 3'b001) |-> ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b100101))
    );
    // Output 111 only when R-type and instru==101010.
    check_inv_out_111: assert property (
        @(posedge clk) (contALU == 3'b111) |-> ((ALUop != 2'b00) && (ALUop != 2'b01) && (instru == 6'b101010))
    );
    // Output 101 only when R-type default path taken.
    check_inv_out_101: assert property (
        @(posedge clk) (contALU == 3'b101) |-> ((ALUop != 2'b00) && (ALUop != 2'b01) &&
                                               (instru != 6'b100000) && (instru != 6'b100010) &&
                                               (instru != 6'b100100) && (instru != 6'b100101) &&
                                               (instru != 6'b101010))
    );
endmodule