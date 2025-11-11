// SVA checker for synchronous_ram
module synchronous_ram_sva #(parameter ADDR_W=10, DATA_W=24, DEPTH=(1<<ADDR_W)) (
    input logic                     clk,
    input logic [DATA_W-1:0]        data_in,
    input logic [ADDR_W-1:0]        write_addr,
    input logic [ADDR_W-1:0]        read_addr,
    input logic                     write_en,
    input logic [DATA_W-1:0]        data_out
);
    // Simple reference model (write-first, read returns previous mem value -> "old data")
    bit [DATA_W-1:0] ref_mem [DEPTH];
    bit              valid   [DEPTH];
    bit              past_valid;

    initial begin
        past_valid = 0;
        foreach (valid[i]) valid[i] = 1'b0;
    end

    // Core correctness: when reading a known location, output must match model
    property p_inputs_known;
        @(posedge clk) !$isunknown({write_en, write_addr, read_addr, data_in});
    endproperty
    assert property (p_inputs_known);

    property p_out_known_when_valid;
        @(posedge clk) valid[read_addr] |-> !$isunknown(data_out);
    endproperty
    assert property (p_out_known_when_valid);

    property p_read_returns_ref;
        @(posedge clk) valid[read_addr] |-> data_out === ref_mem[read_addr];
    endproperty
    assert property (p_read_returns_ref);

    // RAW, one-cycle: read next cycle of same address returns last written data (if not overwritten same cycle)
    property p_raw_one_cycle;
        @(posedge clk) disable iff (!past_valid)
            $past(write_en) && (read_addr == $past(write_addr)) && !(write_en && (write_addr == read_addr))
            |-> data_out === $past(data_in);
    endproperty
    assert property (p_raw_one_cycle);

    // If read_addr is unchanged and no write to that address occurred in prior cycle, data_out must be stable
    property p_stable_when_no_write_to_read_addr;
        @(posedge clk) disable iff (!past_valid)
            (read_addr == $past(read_addr)) && !($past(write_en) && ($past(write_addr) == read_addr))
            |-> $stable(data_out);
    endproperty
    assert property (p_stable_when_no_write_to_read_addr);

    // Reference model update (happens after property sampling on posedge)
    always_ff @(posedge clk) begin
        past_valid <= 1'b1;
        if (write_en) begin
            ref_mem[write_addr] <= data_in;
            valid[write_addr]   <= 1'b1;
        end
    end

    // Functional coverage
    localparam [ADDR_W-1:0] MAX_ADDR = {ADDR_W{1'b1}};

    // Any write, any read of valid addr
    cover property (@(posedge clk) write_en);
    cover property (@(posedge clk) valid[read_addr]);

    // Same-cycle read/write to same address (old-data semantics)
    cover property (@(posedge clk) write_en && (write_addr == read_addr));

    // Read-after-write next cycle same address
    cover property (@(posedge clk) $past(write_en) && (read_addr == $past(write_addr)));

    // Boundary addresses
    cover property (@(posedge clk) write_en && (write_addr == '0));
    cover property (@(posedge clk) valid['0] && (read_addr == '0));
    cover property (@(posedge clk) write_en && (write_addr == MAX_ADDR));
    cover property (@(posedge clk) valid[MAX_ADDR] && (read_addr == MAX_ADDR));

    // Back-to-back writes to same address
    cover property (@(posedge clk) write_en ##1 (write_en && (write_addr == $past(write_addr))));
endmodule

// Bind into DUT
bind synchronous_ram synchronous_ram_sva #(.ADDR_W(10), .DATA_W(24)) u_synchronous_ram_sva (
    .clk, .data_in, .write_addr, .read_addr, .write_en, .data_out
);