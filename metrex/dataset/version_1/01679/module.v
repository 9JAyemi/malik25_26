
module small_fifo_a_dpfifo (
    clock,
    data,
    empty,
    full,
    q,
    rreq,
    sclr,
    usedw,
    wreq
);

    // Module inputs and outputs

    input   clock;
    input   [71:0]  data;
    output   empty;
    output   full;
    output   [71:0]  q;
    input   rreq;
    input   sclr;
    output   [2:0]  usedw;
    input   wreq;

    // Internal registers and wires

    reg  [71:0]   mem [0:7];
    reg  [2:0]   ptr_r;
    reg  [2:0]   ptr_w;
    reg  empty_reg;
    reg  full_reg;
    reg  [2:0]   usedw_reg;

    // Combinational logic

    assign empty = empty_reg;
    assign full = full_reg;
    assign q = mem[ptr_r];
    assign usedw = usedw_reg;

    // Sequential logic

    always @(posedge clock) begin
        if (sclr) begin
            // Reset the FIFO
            ptr_r <= 0;
            ptr_w <= 0;
            empty_reg <= 1;
            full_reg <= 0;
            usedw_reg <= 0;
        end else begin
            if (wreq & !full_reg) begin
                // Write data to the FIFO
                mem[ptr_w] <= data;
                ptr_w <= ptr_w + 1;
                usedw_reg <= usedw_reg + 1;
                if (ptr_w == 8) begin
                    ptr_w <= 0;
                end
                if (usedw_reg == 8) begin
                    full_reg <= 1;
                end
                empty_reg <= 0;
            end
            if (rreq && !empty_reg) begin
                // Read data from the FIFO
                ptr_r <= ptr_r + 1;
                usedw_reg <= usedw_reg - 1;
                if (ptr_r == 8) begin
                    ptr_r <= 0;
                end
                if (usedw_reg == 0) begin
                    empty_reg <= 1;
                end
                full_reg <= 0;
            end
        end
    end

endmodule
