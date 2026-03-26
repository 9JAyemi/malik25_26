module shift_register(
    input clk,
    input areset,  // async active-high reset to zero
    input load,
    input ena,
    input [3:0] data,
    output reg [3:0] q
);

    reg [3:0] shift_reg;
    reg [3:0] shifted_value;

    always @(posedge clk or posedge areset) begin
        if (areset) begin
            shift_reg <= 4'b0;
        end else if (load) begin
            shift_reg <= data;
        end else if (ena) begin
            shift_reg <= {1'b0, shift_reg[3:1]};
        end
    end

    always @* begin
        shifted_value = {1'b0, shift_reg[3:1]};
    end

    always @(posedge clk or posedge areset) begin
        if (areset) begin
            q <= 4'b0;
        end else if (load && ena) begin
            q <= data;
        end else begin
            q <= shifted_value;
        end
    end

endmodule

module top_module(
    input clk,
    input areset,  // async active-high reset to zero
    input load,
    input ena,
    input [3:0] data,
    output [3:0] q
);

    shift_register sr(
        .clk(clk),
        .areset(areset),
        .load(load),
        .ena(ena),
        .data(data),
        .q(q)
    );

endmodule