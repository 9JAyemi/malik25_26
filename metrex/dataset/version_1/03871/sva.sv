// SVA checker for blk_mem_gen
// Concise, high-quality assertions with a lightweight reference model.
// Bind this module to your DUT instance.
//
// Example bind:
// bind blk_mem_gen blk_mem_gen_sva #(.DATA_WIDTH(DATA_WIDTH),
//                                    .ADDR_WIDTH(ADDR_WIDTH),
//                                    .INIT_FILE(INIT_FILE)) u_blk_mem_gen_sva (.*);

module blk_mem_gen_sva #(parameter DATA_WIDTH = 8,
                         parameter ADDR_WIDTH = 8,
                         parameter INIT_FILE  = "")
(
    input  logic                     clk,
    input  logic                     rst,   // not used by DUT, only available if you want to gate checks
    input  logic                     we,
    input  logic [ADDR_WIDTH-1:0]    addr,
    input  logic [DATA_WIDTH-1:0]    din,
    input  logic [DATA_WIDTH-1:0]    dout
);

    // Simple reference model to mirror DUT semantics (read-before-write, registered dout)
    logic [DATA_WIDTH-1:0] ref_mem [0:(1<<ADDR_WIDTH)-1];
    logic                  ref_vld [0:(1<<ADDR_WIDTH)-1];
    logic [DATA_WIDTH-1:0] exp_dout;

    integer i;
    initial begin
        for (i = 0; i < (1<<ADDR_WIDTH); i++) begin
            ref_vld[i] = 1'b0;
        end
        if (INIT_FILE != "") begin
            // DUT uses $readmemh; mirror it so initial contents match
            $readmemh(INIT_FILE, ref_mem);
            for (i = 0; i < (1<<ADDR_WIDTH); i++) begin
                ref_vld[i] = 1'b1;
            end
        end
    end

    always_ff @(posedge clk) begin
        if (we) begin
            ref_mem[addr] <= din;
            ref_vld[addr] <= 1'b1;
        end
        exp_dout <= ref_mem[addr];
    end

    default clocking cb @ (posedge clk); endclocking

    // Basic input sanity (drive known values)
    assert property ( !$isunknown(we) && !$isunknown(addr) )
      else $error("blk_mem_gen: X/Z on we or addr");

    assert property ( we |-> !$isunknown(din) )
      else $error("blk_mem_gen: X/Z on din when we=1");

    // Output must be known when the addressed location is known
    assert property ( ref_vld[addr] |-> !$isunknown(dout) )
      else $error("blk_mem_gen: X/Z on dout for a known location");

    // Golden functional check: dout must equal the reference model
    assert property ( ref_vld[addr] |-> (dout == exp_dout) )
      else $error("blk_mem_gen: dout mismatch vs. reference model");

    // Key scenario coverage
    // Any write
    cover property ( we );

    // Any read-only cycle
    cover property ( !we );

    // Write followed by accessing same address next cycle
    cover property ( we ##1 (addr == $past(addr)) );

    // Boundary address writes
    cover property ( we && (addr == '0) );
    cover property ( we && (addr == {ADDR_WIDTH{1'b1}}) );

endmodule