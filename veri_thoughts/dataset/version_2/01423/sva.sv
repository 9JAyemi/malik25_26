module intr_capturer_sva #(
    parameter int unsigned NUM_INTR = 32
) (
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic [NUM_INTR-1:0]  interrupt_in,
    input  logic                 addr,
    input  logic                 read,
    input  logic [31:0]          rddata,

    // Internal RTL signals (to be connected via bind)
    input  logic [NUM_INTR-1:0]  interrupt_reg,
    input  logic [31:0]          readdata_with_waitstate,
    input  logic [31:0]          act_readdata,
    input  logic [31:0]          readdata_lower_intr,
    input  logic [31:0]          readdata_higher_intr,
    input  logic                 access_lower_32,
    input  logic                 access_higher_32
);

    ///// Reset behavior /////
    // interrupt_reg clears to 0 during reset.
    reset_clears_interrupt_reg: assert property (
        @(posedge clk) !rst_n |-> (interrupt_reg == '0)
    );
    // readdata_with_waitstate clears to 0 during reset.
    reset_clears_readdata_with_waitstate: assert property (
        @(posedge clk) !rst_n |-> (readdata_with_waitstate == 32'b0)
    );
    // rddata clears to 0 during reset.
    reset_clears_rddata: assert property (
        @(posedge clk) !rst_n |-> (rddata == 32'b0)
    );

    ///// Simple structural relationships /////
    // rddata is driven by readdata_with_waitstate.
    rddata_matches_reg: assert property (
        @(posedge clk) disable iff (!rst_n) rddata == readdata_with_waitstate
    );
    // access_lower_32 definition matches read & (addr==0).
    access_lower_definition: assert property (
        @(posedge clk) disable iff (!rst_n) access_lower_32 == (read && (addr == 1'b0))
    );
    // access_higher_32 definition matches read & (addr==1).
    access_higher_definition: assert property (
        @(posedge clk) disable iff (!rst_n) access_higher_32 == (read && (addr == 1'b1))
    );
    // Only one access (lower/higher) can be active at a time.
    access_mutex: assert property (
        @(posedge clk) disable iff (!rst_n) !(access_lower_32 && access_higher_32)
    );
    // act_readdata is the OR of lower and higher read data.
    act_is_or_of_segments: assert property (
        @(posedge clk) disable iff (!rst_n) act_readdata == (readdata_lower_intr | readdata_higher_intr)
    );

    ///// Gating behavior /////
    // No read => both segment data outputs are zero.
    segments_zero_when_no_read: assert property (
        @(posedge clk) disable iff (!rst_n) (!read) |-> ((readdata_lower_intr == 32'b0) && (readdata_higher_intr == 32'b0))
    );
    // No read => act_readdata is zero.
    act_zero_when_no_read: assert property (
        @(posedge clk) disable iff (!rst_n) (!read) |-> (act_readdata == 32'b0)
    );
    // Next cycle after no read => rddata is zero.
    rddata_zero_next_when_no_read: assert property (
        @(posedge clk) disable iff (!rst_n) (!read) |=> (rddata == 32'b0)
    );
    // If lower bank is selected, higher segment must be zero.
    higher_zero_when_lower_selected: assert property (
        @(posedge clk) disable iff (!rst_n) access_lower_32 |-> (readdata_higher_intr == 32'b0)
    );
    // If higher bank is selected, lower segment must be zero.
    lower_zero_when_higher_selected: assert property (
        @(posedge clk) disable iff (!rst_n) access_higher_32 |-> (readdata_lower_intr == 32'b0)
    );
    // When lower selected, act_readdata equals lower segment.
    act_equals_lower_on_lower_select: assert property (
        @(posedge clk) disable iff (!rst_n) access_lower_32 |-> (act_readdata == readdata_lower_intr)
    );
    // When higher selected, act_readdata equals higher segment.
    act_equals_higher_on_higher_select: assert property (
        @(posedge clk) disable iff (!rst_n) access_higher_32 |-> (act_readdata == readdata_higher_intr)
    );

    ///// Segment construction per NUM_INTR /////
    if (NUM_INTR > 32) begin : bigN_checks
        // Lower segment = low 32 interrupt_reg bits masked by access_lower_32.
        lower_segment_bigN: assert property (
            @(posedge clk) disable iff (!rst_n)
                readdata_lower_intr == ( {32{access_lower_32}} & interrupt_reg[31:0] )
        );
        // Higher segment low (NUM_INTR-32) bits = upper interrupt_reg bits masked; upper bits zero.
        higher_segment_bits_bigN: assert property (
            @(posedge clk) disable iff (!rst_n)
                readdata_higher_intr[(NUM_INTR-33):0] == ( ({(NUM_INTR-32){access_higher_32}}) & interrupt_reg[NUM_INTR-1:32] )
        );
        // Higher segment upper unused bits are zero.
        higher_segment_upper_zero_bigN: assert property (
            @(posedge clk) disable iff (!rst_n)
                readdata_higher_intr[31:(NUM_INTR-32)] == '0
        );
    end else begin : smallN_checks
        // Lower segment low NUM_INTR bits = interrupt_reg masked by access; upper bits zero.
        lower_segment_lowbits_smallN: assert property (
            @(posedge clk) disable iff (!rst_n)
                readdata_lower_intr[NUM_INTR-1:0] == ( ({NUM_INTR{access_lower_32}}) & interrupt_reg[NUM_INTR-1:0] )
        );
        // Lower segment upper bits are zero when NUM_INTR<32.
        lower_segment_upper_zero_smallN: assert property (
            @(posedge clk) disable iff (!rst_n)
                readdata_lower_intr[31:NUM_INTR] == '0
        );
        // Higher segment is always zero when NUM_INTR<=32.
        higher_segment_zero_smallN: assert property (
            @(posedge clk) disable iff (!rst_n) readdata_higher_intr == 32'b0
        );
    end

endmodule