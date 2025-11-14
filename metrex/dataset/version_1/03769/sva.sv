// SVA for task_func_test01 and task_func_test02 (shared)
module sva_task_func_acc(input clk,
                         input  [7:0] a,b,c,
                         input  [7:0] x,y,z,w);

  function automatic [7:0] sum_shift4(input [3:0] s1, input [3:0] s2, input [3:0] s3);
    sum_shift4 = s1 + (s2 << 2) + (s3 << 4);
  endfunction

  let z_cons = sum_shift4(4'd1,4'd2,4'd3);
  let z_lhs  = sum_shift4({3'b0,a[0]}, {2'b0,b[5:4]}, (c>>5)[3:0]);
  let sum9   = 9'(x) + 9'(y) + 9'(z);

  // Functional checks
  assert property (@(posedge clk) x == sum_shift4(a[3:0], b[3:0], c[3:0]))
    else $error("x wrong");
  assert property (@(posedge clk) y == sum_shift4(a[7:4], b[5:2], c[3:0]))
    else $error("y wrong");
  assert property (@(posedge clk) z == (z_lhs ^ z_cons))
    else $error("z wrong");
  assert property (@(posedge clk) w == (x + y + z))
    else $error("w wrong");

  // Concise coverage
  cover property (@(posedge clk) z_cons == 8'h39);
  cover property (@(posedge clk) (x!=0 && y!=0 && z!=0) && (w == x + y + z));
  cover property (@(posedge clk) sum9[8]); // overflow carry
endmodule

bind task_func_test01 sva_task_func_acc i_sva_task_func_test01(.clk(clk),.a(a),.b(b),.c(c),.x(x),.y(y),.z(z),.w(w));
bind task_func_test02 sva_task_func_acc i_sva_task_func_test02(.clk(clk),.a(a),.b(b),.c(c),.x(x),.y(y),.z(z),.w(w));


// SVA for task_func_test03 (combinational bitwise AND)
module sva_task_func_test03(input [7:0] din_a, input [7:0] din_b, input [7:0] dout_a);
  always_comb begin
    assert (dout_a == (din_a & din_b)) else $error("dout_a != din_a & din_b");
    cover (dout_a == 8'h00);
    cover (dout_a == 8'hFF);
  end
endmodule

bind task_func_test03 sva_task_func_test03 i_sva_task_func_test03(.din_a(din_a),.din_b(din_b),.dout_a(dout_a));


// SVA for task_func_test04 (functions with local params shadowing module params)
module sva_task_func_test04 #(parameter int unsigned P = 23, parameter int unsigned PX = 42)
                             (input [7:0] in,
                              input [7:0] out1, input [7:0] out2, input [7:0] out3, input [7:0] out4);
  // Expected constants after function/parameter scoping rules
  localparam logic [7:0] T1_ADD = 8'd42;                // local p=42 inside test1
  localparam logic [7:0] T2_ADD = (P + 42) & 8'hFF;     // p2 = p+42, p is module P
  localparam logic [7:0] T3_ADD = (P) & 8'hFF;          // test3 = i + p (module P)
  localparam int unsigned T4_PX = P + 13;               // local px = p+13 (p is module P)
  localparam int unsigned T4_P3 = T4_PX - 37;
  localparam int unsigned T4_P4 = T4_P3 ^ T4_PX;        // 32-bit math per SV rules
  localparam logic [7:0] T4_ADD = T4_P4[7:0];           // function returns [7:0]

  always_comb begin
    assert (out1 == in + T1_ADD) else $error("out1 wrong");
    assert (out2 == in + T2_ADD) else $error("out2 wrong");
    assert (out3 == in + T3_ADD) else $error("out3 wrong");
    assert (out4 == in + T4_ADD) else $error("out4 wrong");
    cover ((in + T2_ADD) < in); // overflow for test2 path
    cover ((in + T4_ADD) < in); // overflow for test4 path
  end
endmodule

bind task_func_test04 sva_task_func_test04 #(.P(p), .PX(px))
  i_sva_task_func_test04(.in(in),.out1(out1),.out2(out2),.out3(out3),.out4(out4));


// SVA for task_func_test05 (task copies input to output on clk)
module sva_task_func_test05(input clk, input data_in, input data_out);
  assert property (@(posedge clk) data_out == data_in)
    else $error("data_out != data_in on clk");
  cover property (@(posedge clk) $changed(data_out));
endmodule

bind task_func_test05 sva_task_func_test05 i_sva_task_func_test05(.clk(clk),.data_in(data_in),.data_out(data_out));