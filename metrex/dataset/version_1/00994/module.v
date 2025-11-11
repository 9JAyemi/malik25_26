
module bcd_counter (
    input clk,
    input reset,
    input [3:1] ena,
    output reg [15:0] q_bcd
);
    always @(posedge reset or posedge clk) begin
        if (reset) begin
            q_bcd <= 16'b0000_0000_0000_0000;
        end else begin
            if (ena[3]) begin
                if (q_bcd[3:0] == 4'b1001) begin
                    q_bcd[3:0] <= 4'b0000;
                    if (q_bcd[7:4] == 4'b1001) begin
                        q_bcd[7:4] <= 4'b0000;
                        if (q_bcd[11:8] == 4'b1001) begin
                            q_bcd[11:8] <= 4'b0000;
                            if (q_bcd[15:12] == 4'b1001) begin
                                q_bcd[15:12] <= 4'b0000;
                            end else begin
                                q_bcd[15:12] <= q_bcd[15:12] + 4'b0001;
                            end
                        end else begin
                            q_bcd[11:8] <= q_bcd[11:8] + 4'b0001;
                        end
                    end else begin
                        q_bcd[7:4] <= q_bcd[7:4] + 4'b0001;
                    end
                end else begin
                    q_bcd[3:0] <= q_bcd[3:0] + 4'b0001;
                end
            end
        end
    end
endmodule
module parallel_load_shift (
    input clk,
    input reset,
    input [7:0] data_in,
    input [2:0] shift_amount,
    output reg [7:0] data_out
);
    always @(posedge reset or posedge clk) begin
        if (reset) begin
            data_out <= 8'b0000_0000;
        end else begin
            if (shift_amount == 3'b000) begin
                data_out <= data_in;
            end else if (shift_amount == 3'b001) begin
                data_out <= {data_in[6:0], data_in[7]};
            end else if (shift_amount == 3'b010) begin
                data_out <= {data_in[5:0], data_in[7:6]};
            end else if (shift_amount == 3'b011) begin
                data_out <= {data_in[4:0], data_in[7:5]};
            end else if (shift_amount == 3'b100) begin
                data_out <= {data_in[3:0], data_in[7:4]};
            end else if (shift_amount == 3'b101) begin
                data_out <= {data_in[2:0], data_in[7:3]};
            end else if (shift_amount == 3'b110) begin
                data_out <= {data_in[1:0], data_in[7:2]};
            end else if (shift_amount == 3'b111) begin
                data_out <= {data_in[0], data_in[7:1]};
            end
        end
    end
endmodule
module sum_module (
    input [15:0] bcd_in,
    input [7:0] shift_in,
    output reg [7:0] sum_out
);
    always @(*) begin
        sum_out = bcd_in[15:8] + shift_in;
    end
endmodule
module top_module (
    input clk,
    input reset,
    output [3:1] ena,
    output [15:0] q_bcd,
    input [7:0] data_in,
    input [2:0] shift_amount,
    output [7:0] data_out,
    output [7:0] sum
);
    assign ena = 4'b111;

    bcd_counter bcd_counter_inst (
        .clk(clk),
        .reset(reset),
        .ena(ena),
        .q_bcd(q_bcd)
    );
    
    parallel_load_shift parallel_load_shift_inst (
        .clk(clk),
        .reset(reset),
        .data_in(data_in),
        .shift_amount(shift_amount),
        .data_out(data_out)
    );
    
    sum_module sum_module_inst (
        .bcd_in(q_bcd),
        .shift_in(data_out),
        .sum_out(sum)
    );
endmodule