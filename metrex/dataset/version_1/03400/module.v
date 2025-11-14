module MMU_MATCH (
    input USER,
    input READ,
    input WRITE,
    input RMW,
    input [2:0] MCR_FLAGS,
    input [31:0] MVALID,
    input [31:12] VADR_R,
    input [31:16] MMU_VA,
    input [1:0] IVAR,
    output VIRTUELL,
    output MMU_HIT,
    output [31:0] UPDATE,
    output reg PROT_ERROR,
    output CI,
    output SEL_PTB1
);

reg [15:0] maske;
wire adr_space, as_sorte, match, alles_ok;
wire [15:0] val_bits, as_bits;
wire ena_prot;
wire zugriff;

assign zugriff = READ | WRITE;

always @(VADR_R) begin
    case (VADR_R[15:12])
        4'h0 : maske = 16'h0001;
        4'h1 : maske = 16'h0002;
        4'h2 : maske = 16'h0004;
        4'h3 : maske = 16'h0008;
        4'h4 : maske = 16'h0010;
        4'h5 : maske = 16'h0020;
        4'h6 : maske = 16'h0040;
        4'h7 : maske = 16'h0080;
        4'h8 : maske = 16'h0100;
        4'h9 : maske = 16'h0200;
        4'hA : maske = 16'h0400;
        4'hB : maske = 16'h0800;
        4'hC : maske = 16'h1000;
        4'hD : maske = 16'h2000;
        4'hE : maske = 16'h4000;
        4'hF : maske = 16'h8000;
    endcase
end

assign VIRTUELL = USER ? MCR_FLAGS[0] : MCR_FLAGS[1];

assign adr_space = IVAR[1] ? IVAR[0] : (MCR_FLAGS[2] & USER);

assign as_sorte = ((MVALID[31:16] & maske) != 16'h0);

assign match = (VADR_R[31:20] == MMU_VA[31:20]) & (adr_space == as_sorte) & ((MVALID[15:0] & maske) != 16'h0000);

assign alles_ok = match & (~WRITE | MMU_VA[17]) & ~PROT_ERROR;

assign MMU_HIT = zugriff ? (VIRTUELL ? alles_ok : 1'b1) : 1'b0;

assign val_bits = IVAR[1] ? (MVALID[15:0] & (match ? ~maske : 16'hFFFF)) : (MVALID[15:0] | maske);
assign as_bits = IVAR[1] ? MVALID[31:16] : (adr_space ? (MVALID[31:16] | maske) : (MVALID[31:16] & ~maske));

assign UPDATE = {as_bits, val_bits};

assign ena_prot = zugriff & VIRTUELL & match;

always @(ena_prot or MMU_VA or USER or WRITE or RMW) begin
    case ({ena_prot, MMU_VA[19:18]})
        3'b100 : PROT_ERROR = USER | WRITE | RMW;
        3'b101 : PROT_ERROR = USER;
        3'b110 : PROT_ERROR = USER & (WRITE | RMW);
        default : PROT_ERROR = 1'b0;
    endcase
end

assign CI = VIRTUELL & MMU_VA[16];
assign SEL_PTB1 = adr_space;

endmodule