module sky130_fd_sc_hd__clkdlybuf4s15_sva #(
    parameter DELAY_SIZE  = 15,
    parameter BUFFER_WIDTH = 1,
    parameter BUFFER_SIZE = DELAY_SIZE * BUFFER_WIDTH
) (
    input logic A,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB,
    input logic [BUFFER_SIZE-1:0] buffer,
    input logic [DELAY_SIZE-1:0] wr_ptr,
    input logic [DELAY_SIZE-1:0] rd_ptr,
    input logic enable
);

    localparam logic [DELAY_SIZE-1:0] LAST_INDEX = BUFFER_SIZE - 1;

    // The internal enable signal is permanently asserted.
    check_enable_const: assert property (
        @(posedge A) enable == 1'b1
    );

    // The write pointer increments by one on each rising edge of A.
    check_wr_ptr_increments: assert property (
        @(posedge A) 1'b1 |=> (wr_ptr == ($past(wr_ptr) + 1'b1))
    );

    // The read pointer wraps to zero after the last valid entry.
    check_rd_ptr_wraps: assert property (
        @(posedge A) (rd_ptr == LAST_INDEX) |=> (rd_ptr == '0)
    );

    // The read pointer increments by one before the wrap point.
    check_rd_ptr_increments: assert property (
        @(posedge A) (rd_ptr < LAST_INDEX) |=> (rd_ptr == ($past(rd_ptr) + 1'b1))
    );

    // The read pointer stays within the valid buffer range after each update.
    check_rd_ptr_in_range: assert property (
        @(posedge A) 1'b1 |=> (rd_ptr <= LAST_INDEX)
    );

    genvar i;
    generate
        for (i = 0; i < BUFFER_SIZE; i = i + 1) begin : gen_buffer_bit_checks
            localparam logic [DELAY_SIZE-1:0] INDEX = i;
            // A selected buffer bit is set high; all other valid bits hold.
            check_buffer_bit_update: assert property (
                @(posedge A) 1'b1 |=> (buffer[i] == (($past(wr_ptr) == INDEX) ? 1'b1 : $past(buffer[i])))
            );
        end
    endgenerate

    // X reflects the buffer entry addressed by rd_ptr on the previous rising edge.
    check_x_updates_from_buffer: assert property (
        @(posedge A) (rd_ptr <= LAST_INDEX) |=> (X == $past(buffer[rd_ptr]))
    );

endmodule

bind sky130_fd_sc_hd__clkdlybuf4s15 sky130_fd_sc_hd__clkdlybuf4s15_sva #(
    .DELAY_SIZE(DELAY_SIZE),
    .BUFFER_WIDTH(BUFFER_WIDTH),
    .BUFFER_SIZE(BUFFER_SIZE)
) sky130_fd_sc_hd__clkdlybuf4s15_sva_inst (
    .A(A),
    .X(X),
    .VPB(VPB),
    .VPWR(VPWR),
    .VGND(VGND),
    .VNB(VNB),
    .buffer(buffer),
    .wr_ptr(wr_ptr),
    .rd_ptr(rd_ptr),
    .enable(enable)
);