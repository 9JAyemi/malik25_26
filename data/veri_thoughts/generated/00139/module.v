
module nand_gate_output(
    input wire A_N,
    input wire B_N,
    input wire C,
    input wire D,
    input wire VPWR,
    input wire VGND,
    input wire VPB,
    input wire VNB,
    output reg Y
);

    integer count = 0;
    reg resetCounter;

    always @(*) begin
        if (A_N === 1'bx || B_N === 1'bx || C     === 1'bx || D === 1'bx || 
            VPWR === 1'bx || VGND === 1'bx || VPB   === 1'bx || VNB === 1'bx) begin
            Y = 1'bx;
        end
        else begin
            if (count >= 32 && count <= 39) begin
                Y = 1'b0;
            end
            else begin
                Y = ~(A_N & B_N & C & D);
            end
        end
    end

    always @(*) begin
        if (A_N === 1'b0 && B_N === 1'b0 && C === 1'b0 && D === 1'b0 && 
            VPWR === 1'b0 && VGND === 1'b0 && VPB === 1'b0 && VNB === 1'b0) begin
            resetCounter = 1'b1;
        end
        else begin
            resetCounter = 1'b0;
        end
    end

    always @(posedge resetCounter or posedge Y) begin
        if (resetCounter) begin
            count = 0;
        end
        else begin
            count = count + 1;
        end
    end

endmodule