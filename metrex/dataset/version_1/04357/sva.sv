// SVA for fpadd_altpriority_encoder_6e8 and submodules.
// Concise checks and coverage; bind to each DUT.

`ifndef FPADD_APE_SVA
`define FPADD_APE_SVA

// 1-bit leaf encoder: q == data, zero == (data==0)
module sva_fpadd_altpriority_encoder_1e8 (
  input  logic [0:0] data,
  input  logic [0:0] q,
  input  logic       zero
);
  always_comb begin
    assert (!$isunknown(data));
    assert (q   == data);
    assert (zero == (data == 1'b0));
    cover (data == 1'b0 && zero && q==1'b0);
    cover (data == 1'b1 && !zero && q==1'b1);
  end
endmodule
bind fpadd_altpriority_encoder_1e8 sva_fpadd_altpriority_encoder_1e8 (.*);

// 2-bit alt encoder: ignores bit[1], uses bit[0]
module sva_fpadd_altpriority_encoder_2e8 (
  input  logic [1:0] data,
  input  logic [0:0] q,
  input  logic       zero
);
  always_comb begin
    assert (!$isunknown(data));
    assert (q    == data[0]);
    assert (zero == (data[0] == 1'b0));
    cover (data[0]==1'b0 && zero && q==1'b0);
    cover (data[0]==1'b1 && !zero && q==1'b1);
  end
endmodule
bind fpadd_altpriority_encoder_2e8 sva_fpadd_altpriority_encoder_2e8 (.*);

// 2-bit priority encoder wrapper: pass-through behavior
module sva_fpadd_priority_encoder_2e8 (
  input  logic [1:0] data,
  input  logic [0:0] q,
  input  logic       zero
);
  always_comb begin
    assert (!$isunknown(data));
    assert (q    == data[0]);
    assert (zero == (data[0] == 1'b0));
    cover (data[0]==1'b0 && zero && q==1'b0);
    cover (data[0]==1'b1 && !zero && q==1'b1);
  end
endmodule
bind fpadd_priority_encoder_2e8 sva_fpadd_priority_encoder_2e8 (.*);

// 3-bit alt encoder: effectively uses only data[0]
module sva_fpadd_altpriority_encoder_3e8 (
  input  logic [2:0] data,
  input  logic [0:0] q,
  input  logic       zero
);
  always_comb begin
    assert (!$isunknown(data));
    assert (q    == data[0]);
    assert (zero == (data[0] == 1'b0));
    cover (data[0]==1'b0 && zero && q==1'b0);
    cover (data[0]==1'b1 && !zero && q==1'b1);
    // hit cases where upper bits vary while outputs remain per data[0]
    cover (data==3'b000);
    cover (data==3'b100);
    cover (data==3'b010);
    cover (data==3'b111);
  end
endmodule
bind fpadd_altpriority_encoder_3e8 sva_fpadd_altpriority_encoder_3e8 (.*);

// 4-bit top encoder: q==10 when data==0 else 11; zero==(data==0)
module sva_fpadd_altpriority_encoder_6e8 (
  input  logic [3:0] data,
  input  logic [1:0] q,
  input  logic       zero
);
  always_comb begin
    assert (!$isunknown(data));
    assert (zero == (data == 4'b0000));
    assert (q == (zero ? 2'b10 : 2'b11));
    assert (q[1] == 1'b1);
    // q never 00/01
    assert (q inside {2'b10,2'b11});

    // Coverage
    cover (data == 4'b0000 && zero && q==2'b10);
    cover (data != 4'b0000 && !zero && q==2'b11);
    cover (data == 4'b0001);
    cover (data == 4'b0010);
    cover (data == 4'b0100);
    cover (data == 4'b1000);
    cover (|data && data[0]==1'b0); // nonzero with LSB 0
    cover (|data && data[0]==1'b1); // nonzero with LSB 1
  end
endmodule
bind fpadd_altpriority_encoder_6e8 sva_fpadd_altpriority_encoder_6e8 (.*);

`endif