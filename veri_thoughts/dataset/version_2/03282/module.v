
module mux6to1_pipeline (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg [3:0] out
);

reg [3:0] stage1_out_0, stage1_out_1, stage1_out_2, stage1_out_3, stage1_out_4, stage1_out_5;
reg [3:0] stage2_out_0, stage2_out_1, stage2_out_2;

always @(*) begin
    case(sel)
        3'b000: begin
            stage1_out_0 <= data0;
            stage1_out_1 <= data1;
            stage1_out_2 <= data2;
            stage1_out_3 <= data3;
            stage1_out_4 <= data4;
            stage1_out_5 <= data5;
        end
        3'b001: begin
            stage1_out_0 <= {data0[3], data0[2], data0[1], data0[0]};
            stage1_out_1 <= {data1[3], data1[2], data1[1], data1[0]};
            stage1_out_2 <= {data2[3], data2[2], data2[1], data2[0]};
            stage1_out_3 <= {data3[3], data3[2], data3[1], data3[0]};
            stage1_out_4 <= {data4[3], data4[2], data4[1], data4[0]};
            stage1_out_5 <= {data5[3], data5[2], data5[1], data5[0]};
        end
        3'b010: begin
            stage1_out_0 <= {data0[3], data0[3], data0[3], data0[3]};
            stage1_out_1 <= {data1[3], data1[3], data1[3], data1[3]};
            stage1_out_2 <= {data2[3], data2[3], data2[3], data2[3]};
            stage1_out_3 <= {data3[3], data3[3], data3[3], data3[3]};
            stage1_out_4 <= {data4[3], data4[3], data4[3], data4[3]};
            stage1_out_5 <= {data5[3], data5[3], data5[3], data5[3]};
        end
        3'b011: begin
            stage1_out_0 <= {data0[0], data0[0], data0[0], data0[0]};
            stage1_out_1 <= {data1[0], data1[0], data1[0], data1[0]};
            stage1_out_2 <= {data2[0], data2[0], data2[0], data2[0]};
            stage1_out_3 <= {data3[0], data3[0], data3[0], data3[0]};
            stage1_out_4 <= {data4[0], data4[0], data4[0], data4[0]};
            stage1_out_5 <= {data5[0], data5[0], data5[0], data5[0]};
        end
        3'b100: begin
            stage1_out_0 <= 4'b0;
            stage1_out_1 <= 4'b0;
            stage1_out_2 <= 4'b0;
            stage1_out_3 <= 4'b0;
            stage1_out_4 <= 4'b0;
            stage1_out_5 <= 4'b0;
        end
        default: begin
            stage1_out_0 <= 4'b0;
            stage1_out_1 <= 4'b0;
            stage1_out_2 <= 4'b0;
            stage1_out_3 <= 4'b0;
            stage1_out_4 <= 4'b0;
            stage1_out_5 <= 4'b0;
        end
    endcase
end

always @(*) begin
    stage2_out_0 <= stage1_out_0 | stage1_out_1;
    stage2_out_1 <= stage1_out_2 | stage1_out_3;
    stage2_out_2 <= stage1_out_4 | stage1_out_5;
end

always @(*) begin
    out <= 3'b000;
    case(sel)
        3'b000: out <= stage2_out_0;
        3'b001: out <= stage2_out_0;
        3'b010: out <= stage2_out_1;
        3'b011: out <= stage2_out_1;
        3'b100: out <= stage2_out_2;
        default: out <= 3'b000;
    endcase
end

endmodule