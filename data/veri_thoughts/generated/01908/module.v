module sram (
    input wire [7:0] address,
    input wire [7:0] data_in,
    input wire clk,
    input wire write_enable,
    output reg [7:0] data_out
);

    always @(posedge clk) begin
        if (write_enable) begin
            data_out <= data_in;
        end
    end

endmodule

module ff_d #(parameter WIDTH = 8) (
    input wire [WIDTH-1:0] D,
    input wire en,
    input wire clk,
    input wire res,
    output reg [WIDTH-1:0] Q
);

    always @(posedge clk or posedge res) begin
        if (res) begin
            Q <= 8'b0;
        end else if (en) begin
            Q <= D;
        end
    end

endmodule

module memory_decoder(
    input wire [7:0] address,
    input wire [7:0] data_in,
    input wire [7:0] switch_in,
    input wire clk,
    input wire res,
    input wire write_enable,
    output wire [7:0] LED_status,
    output wire [7:0] data_out
);

    wire [7:0] memory_data_out;
    wire [7:0] switch_data_out;
    wire mem_write_enable, LED_write_enable;

    // mask write to address 0xff for LED usage
    assign mem_write_enable = write_enable & (~&address);

    // sram block
    sram sram0 (
        .address(address),
        .data_in(data_in),
        .clk(clk),
        .write_enable(mem_write_enable),
        .data_out(memory_data_out)
    );

    // decode LED address
    assign LED_write_enable = write_enable & (&address);

    // LED output driver flip flop
    ff_d #(.WIDTH(8)) led_driver0 (
        .D(data_in),
        .en(LED_write_enable),
        .clk(clk),
        .res(res),
        .Q(LED_status)
    );

    // switch input driver flip flop
    ff_d #(.WIDTH(8)) switch_driver0 (
        .D(switch_in),
        .en(1'b1),
        .clk(clk),
        .res(res),
        .Q(switch_data_out)
    );

    // decode read address
    assign data_out = (~&address) ? memory_data_out : switch_data_out;

endmodule