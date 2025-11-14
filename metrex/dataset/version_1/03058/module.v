module top_module (
    input clk,
    input rst_n,
    input write_en,
    input [7:0] write_addr,
    input [3:0] write_data,
    input read_en,
    input [7:0] read_addr,
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg [3:0] final_output
);

reg [3:0] ram [7:0];
reg [7:0] write_ptr;
reg [7:0] read_ptr;
reg [3:0] ram_out1;
reg [3:0] ram_out2;
reg [3:0] mux_out;

always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
        write_ptr <= 0;
        read_ptr <= 0;
    end else begin
        if (write_en) begin
            ram[write_addr] <= write_data;
            write_ptr <= write_ptr + 1;
        end
        if (read_en) begin
            ram_out1 <= ram[read_addr];
            read_ptr <= read_ptr + 1;
        end
    end
end

always @(posedge clk) begin
    case (sel)
        3'b000: mux_out <= data0;
        3'b001: mux_out <= data1;
        3'b010: mux_out <= data2;
        3'b011: mux_out <= data3;
        3'b100: mux_out <= data4;
        3'b101: mux_out <= data5;
        default: mux_out <= (data0 & 3'b11) & (data1 & 3'b11) & (data2 & 3'b11) & (data3 & 3'b11) & (data4 & 3'b11) & (data5 & 3'b11);
    endcase
end

always @(posedge clk) begin
    ram_out2 <= ram[read_ptr];
    final_output <= ram_out1 | ram_out2 | mux_out;
end

endmodule