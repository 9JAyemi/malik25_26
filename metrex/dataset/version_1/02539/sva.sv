// SVA for my_RAM64X1D2_top and my_RAM64X1D2
// Concise, focused on key functional checks with essential coverage

// Checker for the RAM primitive: models expected behavior and checks dout latency/value
module my_RAM64X1D2_chk (
    input  logic        clk,
    input  logic        we,
    input  logic [5:0]  addr,
    input  logic [7:0]  din,
    input  logic [7:0]  dout
);
    // simple reference model (read-first, synchronous read)
    logic [7:0] model_mem [0:63];
    bit past_valid;

    initial past_valid = 0;
    always_ff @(posedge clk) begin
        past_valid <= 1;
        if (we) model_mem[addr] <= din;
    end

    default clocking cb @(posedge clk); endclocking

    // dout reflects previous-cycle model_mem at previous-cycle addr (read-first)
    assert property ( past_valid |-> dout == $past(model_mem[$past(addr)]) );

    // Coverage: see writes, reads, RAW hazard (write then read same addr)
    cover property ( we );
    cover property ( !we );
    cover property ( past_valid && $past(we) && (addr == $past(addr)) ); // write->read same addr next cycle
endmodule

// Bind checker into both RAM instances
bind my_RAM64X1D2 my_RAM64X1D2_chk u_ram_chk (
    .clk (clk),
    .we  (we),
    .addr(addr),
    .din (din),
    .dout(dout)
);

// Top-level checker: address mapping and output composition
module my_RAM64X1D2_top_chk (
    input  logic        clk,
    input  logic        we,
    input  logic [5:0]  addr,
    input  logic [7:0]  dout,
    // internal wires
    input  logic [5:0]  addr_a,
    input  logic [5:0]  addr_b,
    input  logic [7:0]  dout_a,
    input  logic [7:0]  dout_b
);
    bit past_valid;
    initial past_valid = 0;
    always_ff @(posedge clk) past_valid <= 1;

    default clocking cb @(posedge clk); endclocking

    // Address mapping correctness
    assert property ( addr_a == addr );
    assert property ( addr_b == {1'b0, addr[5:1]} );
    assert property ( addr_b[0] == 1'b0 );

    // Output composition and zero-extension
    assert property ( dout[7:2] == 6'b0 );
    assert property ( dout[1]   == dout_a[0] );
    assert property ( dout[0]   == dout_b[0] );

    // Coverage: exercise both dout bits and addr LSB masking effect
    cover property ( $changed(dout[0]) );
    cover property ( $changed(dout[1]) );
    // Toggle addr[0] while keeping [5:1] stable (addr_b ignores LSB)
    cover property ( past_valid && (addr[5:1] == $past(addr[5:1])) && (addr[0] != $past(addr[0])) );
endmodule

// Bind top-level checker
bind my_RAM64X1D2_top my_RAM64X1D2_top_chk u_top_chk (
    .clk   (clk),
    .we    (we),
    .addr  (addr),
    .dout  (dout),
    .addr_a(addr_a),
    .addr_b(addr_b),
    .dout_a(dout_a),
    .dout_b(dout_b)
);