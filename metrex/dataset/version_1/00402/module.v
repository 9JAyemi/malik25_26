
module top_module (
    input clk,
    input rst,
    input ena,
    input [1:0] shift_dir,
    output wire [3:0] sum
);

    wire [3:0] count;
    wire [3:0] shifted_count;

    binary_counter counter_inst (
        .clk(clk),
        .rst(rst),
        .ena(ena),
        .count(count)
    );

    barrel_shifter shifter_inst (
        .D(count),
        .S(shift_dir),
        .Q(shifted_count)
    );

    assign sum = (shift_dir == 2'b00) ? shifted_count + count :
                (shift_dir == 2'b01) ? shifted_count << 1 :
                (shift_dir == 2'b10) ? shifted_count >> 1 :
                {shifted_count[2:0], shifted_count[3]};

endmodule

module binary_counter (
    input clk,
    input rst,
    input ena,
    output reg [3:0] count
);

    always @ (posedge clk) begin
        if (rst) begin
            count <= 4'b0;
        end else if (ena) begin
            count <= count + 1;
        end
    end

endmodule

module barrel_shifter (
    input [3:0] D,
    input [1:0] S,
    output reg [3:0] Q
);

    always @ (D, S) begin
        case (S)
            2'b00: Q <= D;
            2'b01: Q <= {D[2:0], 1'b0};
            2'b10: Q <= {1'b0, D[3:1]};
            2'b11: Q <= {D[2:0], D[3]};
        endcase
    end

endmodule
