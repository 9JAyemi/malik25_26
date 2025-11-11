
module true_dual_port_ram (
    input clk,
    input read_en,
    input [2:0] read_addr,
    output reg [3:0] read_data,
    input write_en,
    input [2:0] write_addr,
    input [3:0] write_data
);

reg [3:0] ram [7:0];

always @(posedge clk) begin
    if (write_en) begin
        ram[write_addr] <= write_data;
    end
end

always @(*) begin
    if (read_en) begin
        read_data <= ram[read_addr];
    end else begin
        read_data <= 4'b0000;
    end
end

endmodule
module counter (
    input clk,
    input reset,
    output reg [3:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 4'b0000;
    end else begin
        count <= count + 1;
    end
end

endmodule
module register_8bit (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q
);

always @(posedge clk) begin
    if (reset) begin
        q <= 8'h34;
    end else begin
        q <= d;
    end
end

endmodule
module arithmetic_logic (
    input [3:0] counter_data,
    input [7:0] register_data,
    output reg [7:0] result
);

always @(*) begin
    result = {4'b0000, counter_data} + register_data;
end

endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] d,
    input select,
    output reg [7:0] q
);

wire [3:0] counter_output;
wire [7:0] register_output;
wire [7:0] arithmetic_output;

counter counter_inst (
    .clk(clk),
    .reset(reset),
    .count(counter_output)
);

register_8bit register_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(register_output)
);

arithmetic_logic arithmetic_inst (
    .counter_data(counter_output),
    .register_data(register_output),
    .result(arithmetic_output)
);

always @(posedge clk) begin
    if (select) begin
        q <= register_output;
    end else begin
        q <= arithmetic_output;
    end
end

endmodule