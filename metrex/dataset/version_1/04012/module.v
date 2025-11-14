module binary_to_gray (
    input [15:0] binary_in,
    output [15:0] gray_out
);
    assign gray_out = binary_in ^ (binary_in >> 1);
endmodule

module barrel_shifter (
    input [15:0] data_in,
    input [3:0] shift_amount,
    input control,
    output [15:0] data_out
);
    reg [15:0] shifted_data;

    always @(*) begin
        if (control == 1'b0) begin
            shifted_data = data_in << shift_amount;
        end else begin
            shifted_data = data_in >> shift_amount;
        end
    end

    assign data_out = shifted_data;
endmodule

module final_output (
    input [15:0] gray_in,
    input [15:0] shifted_data_in,
    output [15:0] data_out
);
    assign data_out = gray_in & shifted_data_in;
endmodule

module top_module (
    input [15:0] data_in,
    input [3:0] shift_amount,
    input control,
    output [15:0] data_out
);
    wire [15:0] gray_out;
    wire [15:0] shifted_data_out;

    binary_to_gray gray_converter(
        .binary_in(data_in),
        .gray_out(gray_out)
    );

    barrel_shifter shifter(
        .data_in(gray_out),
        .shift_amount(shift_amount),
        .control(control),
        .data_out(shifted_data_out)
    );

    final_output output_generator(
        .gray_in(gray_out),
        .shifted_data_in(shifted_data_out),
        .data_out(data_out)
    );
endmodule