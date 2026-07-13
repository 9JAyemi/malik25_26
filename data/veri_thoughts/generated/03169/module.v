
module top_module (
    input clk, reset,
    input up_down, parallel_load,
    input [6:0] LOAD_IN,
    output reg [6:0] ripple_counter_out,
    output ser_out
);

reg [6:0] parallel_load_data;
wire [6:0] ripple_counter;
wire [2:0] shift_register_data;

up_down_counter counter (
    .clk(clk),
    .reset(reset),
    .LD(parallel_load),
    .UD(up_down),
    .LOAD_IN(LOAD_IN[3:0]),
    .Q(ripple_counter)
);

shift_register shift_reg (
    .clk(clk),
    .load(parallel_load),
    .serial_in(ripple_counter[6]),
    .out(shift_register_data)
);

always @(posedge clk) begin
    if (reset) begin
        ripple_counter_out <= 7'b0;
        parallel_load_data <= 7'b0;
    end else begin
        if (parallel_load) begin
            parallel_load_data <= LOAD_IN;
        end
        ripple_counter_out <= ripple_counter;
    end
end

assign ser_out = shift_register_data[2];

endmodule

module up_down_counter (
    input clk, reset, LD, UD,
    input [3:0] LOAD_IN,
    output reg [6:0] Q
);

always @(posedge clk) begin
    if (reset) begin
        Q <= 7'b0;
    end else begin
        if (LD) begin
            Q <= LOAD_IN;
        end else if (UD) begin
            Q <= Q + 1;
        end else begin
            Q <= Q - 1;
        end
    end
end

endmodule

module shift_register (
    input clk,
    input load,
    input serial_in,
    output reg [2:0] out
);

always @(posedge clk) begin
    if (load) begin
        out <= 3'b0;
    end else begin
        out <= {out[1:0], serial_in};
    end
end

endmodule
