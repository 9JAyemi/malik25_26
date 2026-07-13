module bit_summing_circuit ( input [15:0] in, output reg [3:0] out );

    always @* begin
        out = {in[14], in[12], in[10], in[8]} + {in[7], in[5], in[3], in[1]};
    end

endmodule

module ring_counter ( input clk, input reset, output reg [2:0] out );

    always @(posedge clk) begin
        if (reset) begin
            out <= 3'b000;
        end else begin
            out <= {out[1:0], out[2]};
        end
    end

endmodule

module final_output ( input [3:0] bit_sum, input [2:0] ring_count, output reg [3:0] out );

    always @* begin
        out = bit_sum + ring_count;
    end

endmodule

module top_module ( input clk, input [15:0] in, output reg [3:0] q );

    wire [3:0] bit_sum;
    wire [2:0] ring_count;
    wire [3:0] final_out;

    bit_summing_circuit bit_sum_circuit ( .in(in), .out(bit_sum) );
    ring_counter ring_counter_inst ( .clk(clk), .reset(q[0]), .out(ring_count) );
    final_output final_out_inst ( .bit_sum(bit_sum), .ring_count(ring_count), .out(final_out) );

    always @* begin
        q <= final_out;
    end

endmodule