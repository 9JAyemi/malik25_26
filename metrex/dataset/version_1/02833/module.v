module top_module (
    input clk,
    input reset,
    input slowena,
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    input [3:0] threshold,
    output [3:0] count,
    output high_if_count_greater_than_threshold,
    output [3:0] final_output
);

    // Priority Encoder for select signal
    wire [2:0] sel_priority;
    priority_encoder pe(sel, sel_priority);

    // 6-to-1 Multiplexer
    wire [3:0] mux_output;
    assign mux_output = (sel_priority == 0) ? data0 :
                        (sel_priority == 1) ? data1 :
                        (sel_priority == 2) ? data2 :
                        (sel_priority == 3) ? data3 :
                        (sel_priority == 4) ? data4 :
                        (sel_priority == 5) ? data5 :
                        4'b1; // Output 1 if select signal is outside range

    // 4-bit Binary Up Counter
    reg [3:0] count_reg;
    always @(posedge clk) begin
        if (reset) begin
            count_reg <= 4'b0;
        end else if (slowena) begin
            count_reg <= count_reg + 1;
        end
    end
    assign count = count_reg;

    // 4-bit Comparator
    wire [3:0] threshold_value = threshold;
    assign high_if_count_greater_than_threshold = (count_reg >= threshold_value);

    // Bitwise AND module
    wire [3:0] and_output;
    assign and_output = mux_output & high_if_count_greater_than_threshold;

    // Final output
    assign final_output = and_output;

endmodule

// Priority Encoder module
module priority_encoder (
    input [2:0] in,
    output reg [2:0] out
);
    always @* begin
        case (in)
            3'b000: out = 3'b000;
            3'b001: out = 3'b001;
            3'b010: out = 3'b010;
            3'b011: out = 3'b011;
            3'b100: out = 3'b100;
            3'b101: out = 3'b101;
            default: out = 3'b111; // Output 111 if input is outside range
        endcase
    end
endmodule