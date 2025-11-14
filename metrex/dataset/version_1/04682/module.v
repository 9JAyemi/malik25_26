module data_buffer #(
    parameter DEPTH = 8,
    parameter L = 3,
    parameter dat_width = 8
)(
    input CLK, // System clock for both read and write operations
    input Rst, // Reset
    input Wren, // Write enable
    input Rden, // Read enable
    input [L-1:0] adr_wr_i, // Write address
    input [L-1:0] adr_rd_i, // Read address
    input [dat_width-1:0] Datain, // Input data
    output reg [dat_width-1:0] Dataout, // Output data
    output reg Full, // Full signal
    output reg Empty // Empty signal
);

    reg [dat_width-1:0] data_ram [0:DEPTH-1]; // Data buffer
    reg [L-1:0] status_cnt; // Status counter

    always @(posedge CLK) begin
        if (Rst) begin
            status_cnt <= 0;
            Dataout <= 0; // Clear Dataout on reset
        end else begin
            if (Wren) begin
                data_ram[adr_wr_i] <= Datain; // Perform write operation
                if (!Rden && status_cnt < DEPTH) status_cnt <= status_cnt + 1;
            end
            if (Rden && status_cnt > 0) begin
                Dataout <= data_ram[adr_rd_i]; // Perform read operation
                status_cnt <= status_cnt - 1;
            end
        end
    end
    
    always @(posedge CLK or posedge Rst) begin
        if (Rst) begin
            Full <= 0;
            Empty <= 1;
        end else begin
            Full <= (status_cnt == DEPTH);
            Empty <= (status_cnt == 0);
        end
    end
endmodule
