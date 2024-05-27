#include <stdio.h>
#include <stdlib.h>

#define COUNT 10

struct Node
{
	int data;
	struct Node *left, *right;
};

struct Node *newNode(int data)
{
	struct Node *node = (struct Node *)malloc(sizeof(struct Node));
	node->data = data;
	node->left = node->right = NULL;
	return node;
}

struct Node *insertNode(struct Node *node, int data)
{
	if (node == NULL)
		return newNode(data);

	if (data < node->data)
		node->left = insertNode(node->left, data);
	else if (data > node->data)
		node->right = insertNode(node->right, data);

	return node;
}

struct Node *minValueNode(struct Node *node)
{
	struct Node *current = node;

	while (current && current->left != NULL)
		current = current->left;

	return current;
}

struct Node *deleteNode(struct Node *root, int data)
{
	if (root == NULL)
		return root;

	if (data < root->data)
		root->left = deleteNode(root->left, data);
	else if (data > root->data)
		root->right = deleteNode(root->right, data);
	else
	{
		if (root->left == NULL)
		{
			struct Node *temp = root->right;
			free(root);
			return temp;
		}
		else if (root->right == NULL)
		{
			struct Node *temp = root->left;
			free(root);
			return temp;
		}

		struct Node *temp = minValueNode(root->right);

		root->data = temp->data;

		root->right = deleteNode(root->right, temp->data);
	}
	return root;
}

void print2DUtil(struct Node *root, int space)
{
	if (root == NULL)
		return;

	space += COUNT;

	print2DUtil(root->right, space);

	printf("\n");
	for (int i = COUNT; i < space; i++)
		printf(" ");
	printf("%d\n", root->data);

	print2DUtil(root->left, space);
}

void print2D(struct Node *root)
{
	print2DUtil(root, 0);
}

int main()
{
	struct Node *root = NULL;
	root = insertNode(root, 50);
	root = insertNode(root, 30);
	root = insertNode(root, 20);
	root = insertNode(root, 40);
	root = insertNode(root, 70);
	root = insertNode(root, 60);
	root = insertNode(root, 80);

	print2D(root);

	printf("\nDelete 20\n");
	root = deleteNode(root, 20);
	print2D(root);

	printf("\nInsert 25\n");
	root = insertNode(root, 25); // New insertion
	print2D(root);

	printf("\nDelete 30\n");
	root = deleteNode(root, 30);
	print2D(root);

	printf("\nInsert 35\n");
	root = insertNode(root, 35); // New insertion
	print2D(root);

	printf("\nDelete 50\n");
	root = deleteNode(root, 50);
	print2D(root);

	return 0;
}