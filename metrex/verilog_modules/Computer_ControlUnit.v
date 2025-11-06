
module Computer_ControlUnit(
    output reg [7:0] CONST_bus_out,
    output reg [6:0] CNTRL_bus_out,
    output reg [2:0] COUNTER_bus_out,
    input [15:0] INSTR_bus_in,
    input [3:0] ULA_FLAG_bus_in,
    input [15:0] ADDR_bus_in,
    input CLK,
    input RST
);

parameter DR_WIDTH = 3;
parameter SA_WIDTH = DR_WIDTH;
parameter SB_WIDTH = DR_WIDTH;
parameter OPCODE_WIDTH = 7;
parameter FS_WIDTH = 4;
parameter CNTRL_FLAGS_WIDTH = 7;
parameter ULA_FLAG_WIDTH = 4;
parameter CNTRL_WIDTH = DR_WIDTH+SA_WIDTH+SB_WIDTH+FS_WIDTH+CNTRL_FLAGS_WIDTH;

reg [DR_WIDTH-1:0] DR;
reg [SA_WIDTH-1:0] SA;
reg [SB_WIDTH-1:0] SB;
reg [OPCODE_WIDTH-1:0] OPCODE;
reg [FS_WIDTH-1:0] FS;
reg [CNTRL_FLAGS_WIDTH-1:0] CNTRL_FLAGS;

always @(posedge CLK, posedge RST) begin
    if (RST) begin
        DR <= 3'b0;
        SA <= 3'b0;
        SB <= 3'b0;
        OPCODE <= 7'b0;
        FS <= 4'b0;
        CNTRL_FLAGS <= 7'b0;
    end else begin
        DR <= INSTR_bus_in[15:13];
        SA <= INSTR_bus_in[12:10];
        SB <= INSTR_bus_in[9:7];
        OPCODE <= INSTR_bus_in[6:0];
        case (OPCODE)
            7'b0000000: begin // ADD
                FS <= 4'b0001;
                CNTRL_FLAGS <= 7'b0000001;
            end
            7'b0000001: begin // SUB
                FS <= 4'b0010;
                CNTRL_FLAGS <= 7'b0000001;
            end
            7'b0000010: begin // AND
                FS <= 4'b0100;
                CNTRL_FLAGS <= 7'b0000001;
            end
            7'b0000011: begin // OR
                FS <= 4'b0101;
                CNTRL_FLAGS <= 7'b0000001;
            end
            7'b0000100: begin // XOR
                FS <= 4'b0110;
                CNTRL_FLAGS <= 7'b0000001;
            end
            7'b0000101: begin // NOT
                FS <= 4'b0111;
                CNTRL_FLAGS <= 7'b0000001;
            end
            7'b0000110: begin // LD
                FS <= 4'b0000;
                CNTRL_FLAGS <= 7'b0000000;
            end
            7'b0000111: begin // ST
                FS <= 4'b0000;
                CNTRL_FLAGS <= 7'b0000010;
            end
            default: begin
                FS <= 4'b0000;
                CNTRL_FLAGS <= 7'b0000000;
            end
        endcase

        // Fix the assignments to constant values
        CONST_bus_out <= 8'h00;
        CNTRL_bus_out <= {DR, SA, SB, FS, CNTRL_FLAGS};
        COUNTER_bus_out <= 3'b000;
    end
end

endmodule
