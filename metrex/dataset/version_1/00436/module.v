
module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [3:0] write_data, // 4-bit input for the RAM module
    input [2:0] write_addr, // Address input for the RAM module
    input write_en, // Write enable input for the RAM module
    input [3:0] in, // Input signal for the input signal detection module
    input select, // Select input to choose between RAM module and functional module
    input [2:0] read_addr, // Address input for the functional module
    input read_en, // Read enable input for the functional module
    output [3:0] read_data // 4-bit output from the active module
);

wire [3:0] ram_data;
wire [3:0] func_data;
wire [3:0] in_detect;

dual_port_ram dp_ram (
    .clk(clk),
    .reset(reset),
    .write_data(write_data),
    .write_addr(write_addr),
    .write_en(write_en),
    .read_data(ram_data),
    .read_addr(read_addr),
    .read_en(read_en)
);

input_signal_detection isd (
    .clk(clk),
    .in(in),
    .out(in_detect)
);

functional_module fm (
    .ram_data(ram_data),
    .in_detect(in_detect),
    .out(func_data)
);

assign read_data = select ? func_data : ram_data;

endmodule
module dual_port_ram (
    input clk,
    input reset,
    input [3:0] write_data,
    input [2:0] write_addr,
    input write_en,
    output [3:0] read_data,
    input [2:0] read_addr,
    input read_en
);

reg [3:0] memory [7:0];

always @(posedge clk) begin
    if (reset) begin
        memory[write_addr] <= 4'b1111;
    end else if (write_en) begin
        memory[write_addr] <= write_data;
    end
end

assign read_data = memory[read_addr];

endmodule
module input_signal_detection (
    input clk,
    input [3:0] in,
    output [3:0] out
);

reg [3:0] prev_in;

always @(posedge clk) begin
    prev_in <= in;
end

assign out = (prev_in == 4'b0001) & (in == 4'b0000) ? 4'b1111 : 4'b0000;

endmodule
module functional_module (
    input [3:0] ram_data,
    input [3:0] in_detect,
    output [3:0] out
);

assign out = in_detect ? ram_data : 4'b0000;

endmodule