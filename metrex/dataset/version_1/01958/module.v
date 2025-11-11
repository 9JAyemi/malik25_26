
module cpu_ctl(
    input wire [5:0] op, func,
    input wire equal_result,
    output wire JR, J, JAL, LW, WREG, WMEM, RDorRT, SE, SA, IorR, BJ,
    output reg [4:0] Aluc
);

    wire r_type = ~op[5] & ~op[4] & ~op[3] & ~op[2] & ~op[1] & ~op[0];
    wire i_jr = r_type & ~func[5] & ~func[4] & func[3] & ~func[2] & ~func[1] & ~func[0];
    wire i_sll = r_type & ~func[5] & ~func[4] & ~func[3] & ~func[2] & ~func[1] & ~func[0];
    wire i_srl = r_type & ~func[5] & ~func[4] & ~func[3] & ~func[2] & func[1] & ~func[0];
    wire i_sra = r_type & ~func[5] & ~func[4] & ~func[3] & ~func[2] & func[1] & func[0];

    wire i_addi, i_addiu, i_andi, i_ori, i_xori, i_lui, i_lw, i_sw, i_slti, i_sltiu;
    wire b_type, i_beq, i_bne;
    wire i_j, i_jal;

    wire i_type = i_addi | i_addiu | i_andi | i_ori | i_xori | i_lui | i_lw | i_sw | i_slti | i_sltiu;

    assign i_addi = ~op[5] & ~op[4] & op[3] & ~op[2] & ~op[1] & ~op[0];
    assign i_addiu = ~op[5] & ~op[4] & op[3] & ~op[2] & ~op[1] & op[0];
    assign i_andi = ~op[5] & ~op[4] & op[3] & op[2] & ~op[1] & ~op[0];
    assign i_ori = ~op[5] & ~op[4] & op[3] & op[2] & ~op[1] & op[0];
    assign i_xori = ~op[5] & ~op[4] & op[3] & op[2] & op[1] & ~op[0];
    assign i_lui = ~op[5] & ~op[4] & op[3] & op[2] & op[1] & op[0];
    assign i_lw = op[5] & ~op[4] & ~op[3] & ~op[2] & op[1] & op[0];
    assign i_sw = op[5] & ~op[4] & op[3] & ~op[2] & op[1] & op[0];
    assign i_slti = ~op[5] & ~op[4] & op[3] & ~op[2] & op[1] & ~op[0];
    assign i_sltiu = ~op[5] & ~op[4] & op[3] & ~op[2] & op[1] & op[0];

    assign b_type = i_beq | i_bne;
    assign i_beq = ~op[5] & ~op[4] & ~op[3] & op[2] & ~op[1] & ~op[0];
    assign i_bne = ~op[5] & ~op[4] & ~op[3] & op[2] & ~op[1] & op[0];

    assign i_j = ~op[5] & ~op[4] & ~op[3] & ~op[2] & op[1] & ~op[0];
    assign i_jal = ~op[5] & ~op[4] & ~op[3] & ~op[2] & op[1] & op[0];

    assign JR = i_jr;
    assign J = i_j;
    assign JAL = i_jal;
    assign LW = i_lw;
    assign WREG = i_jal | (IorR & ~i_sw) | (r_type & ~i_jr);
    assign WMEM = i_sw;
    assign RDorRT = r_type & ~i_jr;
    assign SE = i_addi | i_addiu | i_lw | i_sw | i_slti;
    assign SA = i_sll | i_srl | i_sra;
    assign IorR = i_type & ~b_type;
    assign BJ = (i_beq & equal_result) | (i_bne & ~equal_result);

    always @(*) begin
        case ({op, func})
            6'b000000: Aluc = func[3:0]; // R-Type
            6'b001000: Aluc = 4'b0010; // ADDI
            6'b001001: Aluc = 4'b0011; // ADDIU
            6'b001100: Aluc = 4'b0000; // ANDI
            6'b001101: Aluc = 4'b0101; // ORI
            6'b001110: Aluc = 4'b0110; // XORI
            6'b001010: Aluc = 4'b0111; // SLTI
            6'b001011: Aluc = 4'b1000; // SLTIU
            6'b100011: Aluc = 4'b0001; // LW
            6'b101011: Aluc = 4'b0001; // SW
            default: Aluc = 4'b0000; // Default to 0
        endcase
    end

endmodule