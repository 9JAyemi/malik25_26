
module comparator (
    comp1,
    v1_reg
);

    output comp1;
    input [5:0] v1_reg;

    wire [4:0] carrynet;
    wire [1:0] ms_carry;

    // Carry Network
    assign carrynet = {1'b0, v1_reg[3:0] + 4'b0001};

    // MSB Carry
    assign {ms_carry[1],comp1,carrynet[4]} = carrynet[3] + v1_reg[5:4] + 2'b01;

endmodule