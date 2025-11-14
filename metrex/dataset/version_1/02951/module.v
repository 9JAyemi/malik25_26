
module rotator (
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q);

    reg [99:0] shift_reg;
    wire [99:0] shifted_data;

    assign shifted_data = {shift_reg[0], shift_reg[99:1]};

    always @(posedge clk) begin
        if (load) begin
            shift_reg <= data;
        end else begin
            case (ena)
                2'b00: shift_reg <= shifted_data;
                2'b01: shift_reg <= {shift_reg[99], shift_reg[99:1]};
                2'b10: shift_reg <= {shift_reg[0], shift_reg[99:1]};
                2'b11: shift_reg <= shift_reg;
            endcase
        end
    end

    assign q = shift_reg;
endmodule
module top_module(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q);

    rotator rotator_inst(
        .clk(clk),
        .load(load),
        .ena(ena),
        .data(data),
        .q(q)
    );

endmodule