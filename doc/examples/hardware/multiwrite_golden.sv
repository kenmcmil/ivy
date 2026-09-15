// Golden model for multiwrite.ivy: two nonblocking writes in one clock. When the
// addresses differ both land; when they coincide the later (mem[b]<=y) wins, which
// is exactly a two-write-port memory with the later port prioritized.
module top ( \posedge , rst, a, b, x, y, r, rd );
    input \posedge ; input rst;
    input [3:0] a; input [3:0] b; input [7:0] x; input [7:0] y; input [3:0] r;
    output [7:0] rd;
    reg [7:0] mem [0:15];
    assign rd = mem[r];
    always @(posedge \posedge ) begin
        mem[a] <= x;
        mem[b] <= y;
    end
endmodule
