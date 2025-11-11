
module nand3_gate(input A, input B, input C, output Y);

    // Inputs are registered
    reg A_reg;
    reg B_reg;
    reg C_reg;

    // Outputs are wires
    wire Y_and;

    // Connect to power and ground
    supply1 VDD;
    supply0 VSS;

    // Instantiate buffers
    buf A_buf (A, A_reg);
    buf B_buf (B, B_reg);
    buf C_buf (C, C_reg);
    buf Y_buf (Y_and, Y);

    // Instantiate NAND gates
    nand (Y_and, A_reg, B_reg, C_reg); // 3-input NAND gate

endmodule