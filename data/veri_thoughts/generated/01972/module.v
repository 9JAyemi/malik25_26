
module barrel_shifter (
    input [7:0] data,
    input [1:0] shift,
    output [7:0] shifted_data
);

    assign shifted_data = (shift[1]) ? {data[0], data[7:1]} : 
                          (shift[0]) ? {data[1:0], data[7:2]} : 
                                       {data[2:0], data[7:3]};

endmodule

module shift_register (
    input clk,
    input load,
    input [7:0] data_in,
    output [7:0] data_out
);

    reg [7:0] shift_reg;

    always @(posedge clk) begin
        if (load) begin
            shift_reg <= data_in;
        end else begin
            shift_reg <= {shift_reg[6:0], shift_reg[7]};
        end
    end

    assign data_out = shift_reg;

endmodule

module functional_module (
    input [7:0] shifted_data,
    input [7:0] shift_reg_data,
    output [7:0] sum
);

    assign sum = shifted_data + shift_reg_data;

endmodule

module top_module (
    input clk,
    input reset,
    input [7:0] data,
    input [1:0] shift,
    input load,
    output [7:0] q
);

    wire [7:0] shifted_data;
    wire [7:0] shift_reg_data;
    wire [7:0] sum;

    barrel_shifter barrel_shifter_inst (
        .data(data),
        .shift(shift),
        .shifted_data(shifted_data)
    );

    shift_register shift_register_inst (
        .clk(clk),
        .load(load),
        .data_in(shifted_data),
        .data_out(shift_reg_data)
    );

    functional_module functional_module_inst (
        .shifted_data(shifted_data),
        .shift_reg_data(shift_reg_data),
        .sum(sum)
    );

    assign q = sum;

endmodule
