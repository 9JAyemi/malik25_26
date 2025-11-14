
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input shift_left, // Control input to shift register to the left
    input shift_right,// Control input to shift register to the right
    output [3:0] q    // 4-bit output from the functional module
);

    wire [3:0] counter_out;
    wire [3:0] shift_register_out;
    wire [3:0] functional_out;

    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .count(counter_out)
    );

    shift_register shift_register_inst (
        .clk(clk),
        .reset(reset),
        .shift_left(shift_left),
        .shift_right(shift_right),
        .data_in(counter_out), // Updated to select 4 bits
        .data_out(shift_register_out)
    );

    functional_module functional_inst (
        .counter_in(counter_out),
        .shift_register_in(shift_register_out),
        .functional_out(functional_out)
    );

    assign q = functional_out;

endmodule
module counter (
    input clk,
    input reset,
    output reg [3:0] count
);
    always @(posedge clk or posedge reset) begin // Updated sensitivity list
        if (reset) begin
            count <= 4'b0000;
        end else begin
            count <= count + 4'b0001; // Updated to add 4-bit value
        end
    end
endmodule
module shift_register (
    input clk,
    input reset,
    input shift_left,
    input shift_right,
    input [3:0] data_in, // Updated input data width
    output reg [3:0] data_out
);
    always @(posedge clk or posedge reset) begin // Updated sensitivity list
        if (reset) begin
            data_out <= 4'b0000;
        end else begin
            if (shift_left) begin
                data_out <= {data_out[2:0], data_in[3]};
            end else if (shift_right) begin
                data_out <= {data_in[0], data_out[3:1]};
            end
        end
    end
endmodule
module functional_module (
    input [3:0] counter_in,
    input [3:0] shift_register_in,
    output reg [3:0] functional_out
);
    always @(*) begin
        functional_out = (counter_in + shift_register_in) ^ 4'b1010;
    end
endmodule